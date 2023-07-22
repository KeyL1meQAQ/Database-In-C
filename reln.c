// reln.c ... functions on Relations
// part of Multi-attribute Linear-hashed Files
// Last modified by John Shepherd, July 2019

#include "defs.h"
#include "reln.h"
#include "page.h"
#include "tuple.h"
#include "chvec.h"
#include "bits.h"
#include "hash.h"
#include "query.h"

#define HEADERSIZE (3*sizeof(Count)+sizeof(Offset))

struct RelnRep {
	Count  nattrs; // number of attributes
	Count  depth;  // depth of main data file
	Offset sp;     // split pointer
    Count  npages; // number of main data pages
    Count  ntups;  // total number of tuples
	ChVec  cv;     // choice vector
	char   mode;   // open for read/write
	FILE  *info;   // handle on info file
	FILE  *data;   // handle on data file
	FILE  *ovflow; // handle on ovflow file
};

// create a new relation (three files)

Status newRelation(char *name, Count nattrs, Count npages, Count d, char *cv)
{
    char fname[MAXFILENAME];
	Reln r = malloc(sizeof(struct RelnRep));
	r->nattrs = nattrs; r->depth = d; r->sp = 0;
	r->npages = npages; r->ntups = 0; r->mode = 'w';
	assert(r != NULL);
	if (parseChVec(r, cv, r->cv) != OK) return ~OK;
	sprintf(fname,"%s.info",name);
	r->info = fopen(fname,"w");
	assert(r->info != NULL);
	sprintf(fname,"%s.data",name);
	r->data = fopen(fname,"w");
	assert(r->data != NULL);
	sprintf(fname,"%s.ovflow",name);
	r->ovflow = fopen(fname,"w");
	assert(r->ovflow != NULL);
	int i;
	for (i = 0; i < npages; i++) addPage(r->data);
	closeRelation(r);
	return 0;
}

// check whether a relation already exists

Bool existsRelation(char *name)
{
	char fname[MAXFILENAME];
	sprintf(fname,"%s.info",name);
	FILE *f = fopen(fname,"r");
	if (f == NULL)
		return FALSE;
	else {
		fclose(f);
		return TRUE;
	}
}

// set up a relation descriptor from relation name
// open files, reads information from rel.info

Reln openRelation(char *name, char *mode)
{
	Reln r;
	r = malloc(sizeof(struct RelnRep));
	assert(r != NULL);
	char fname[MAXFILENAME];
	sprintf(fname,"%s.info",name);
	r->info = fopen(fname,mode);
	assert(r->info != NULL);
	sprintf(fname,"%s.data",name);
	r->data = fopen(fname,mode);
	assert(r->data != NULL);
	sprintf(fname,"%s.ovflow",name);
	r->ovflow = fopen(fname,mode);
	assert(r->ovflow != NULL);
	// Naughty: assumes Count and Offset are the same size
	int n = fread(r, sizeof(Count), 5, r->info);
	assert(n == 5);
	n = fread(r->cv, sizeof(ChVecItem), MAXCHVEC, r->info);
	assert(n == MAXCHVEC);
	r->mode = (mode[0] == 'w' || mode[1] =='+') ? 'w' : 'r';
	return r;
}

// release files and descriptor for an open relation
// copy latest information to .info file

void closeRelation(Reln r)
{
	// make sure updated global data is put in info
	// Naughty: assumes Count and Offset are the same size
	if (r->mode == 'w') {
		fseek(r->info, 0, SEEK_SET);
		// write out core relation info (#attr,#pages,d,sp)
		int n = fwrite(r, sizeof(Count), 5, r->info);
		assert(n == 5);
		// write out choice vector
		n = fwrite(r->cv, sizeof(ChVecItem), MAXCHVEC, r->info);
		assert(n == MAXCHVEC);
	}
	fclose(r->info);
	fclose(r->data);
	fclose(r->ovflow);
	free(r);
}

PageID addTuple(Reln r, PageID p, Tuple t) {
    Page pg = getPage(r->data,p);
    if (addToPage(pg,t) == OK) {
        putPage(r->data,p,pg);
        return p;
    }
    // primary data page full
    if (pageOvflow(pg) == NO_PAGE) {
        // add first overflow page in chain
        PageID newp = addPage(r->ovflow);
        pageSetOvflow(pg,newp);
        putPage(r->data,p,pg);
        Page newpg = getPage(r->ovflow,newp);
        // can't add to a new page; we have a problem
        if (addToPage(newpg,t) != OK) return NO_PAGE;
        putPage(r->ovflow,newp,newpg);
        return p;
    }
    else {
        // scan overflow chain until we find space
        // worst case: add new ovflow page at end of chain
        Page ovpg, prevpg = NULL;
        PageID ovp, prevp = NO_PAGE;
        ovp = pageOvflow(pg);
        while (ovp != NO_PAGE) {
            ovpg = getPage(r->ovflow, ovp);
            if (addToPage(ovpg,t) != OK) {
                prevp = ovp; prevpg = ovpg;
                ovp = pageOvflow(ovpg);
            }
            else {
                if (prevpg != NULL) free(prevpg);
                putPage(r->ovflow,ovp,ovpg);
                return p;
            }
        }
        // all overflow pages are full; add another to chain
        // at this point, there *must* be a prevpg
        assert(prevpg != NULL);
        // make new ovflow page
        PageID newp = addPage(r->ovflow);
        // insert tuple into new page
        Page newpg = getPage(r->ovflow,newp);
        if (addToPage(newpg,t) != OK) return NO_PAGE;
        putPage(r->ovflow,newp,newpg);
        // link to existing overflow chain
        pageSetOvflow(prevpg,newp);
        putPage(r->ovflow,prevp,prevpg);
        return p;
    }
    return NO_PAGE;
}

void distributeTuples(PageID old, Reln r) {
    PageID new = addPage(dataFile(r)); // Add a new page to datafile
    r->npages++;

    Page oldPage = getPage(dataFile(r), old); // Get the old primary page
    PageID currentPageID = old; // Get the current page id
    int isTraverseOverflow = 0; // Is examining an overflow page?

    Page replacePage = newPage(); // Create a new page for place tuples still in old buckets
    // The page id of next page that next replacing page is going to replace
    // Also the overflow page id of current replace page.
    PageID nextReplacePageID = pageOvflow(oldPage);
    PageID curReplacePageID = old; // The page id of the page that current replace page is going to replace
    pageSetOvflow(replacePage, nextReplacePageID);
    int isReplaceOverflow = 0; // Is going to replace an overflow page?

    int npages = 0; // How many buckets in old page
    int npagesReplaced = 0; // How many buckets has been replaced

    while (currentPageID != NO_PAGE) { // Loop entire primary page and overflow chain
        free(oldPage); // Release the memory of previous examined page
        // Get a page for examining
        oldPage = isTraverseOverflow ? getPage(ovflowFile(r), currentPageID) : getPage(dataFile(r), currentPageID);

        Count ntuples = pageNTuples(oldPage); // How many tuples in this page
        Count examinedTuples = 0; // How many tuples are examined
        char *c = pageData(oldPage);

        while (examinedTuples < ntuples) { // If there are more tuple in current page
            Bits hash = tupleHash(r, c);
            PageID newID = getLower(hash, r->depth + 1); // Generate page id by depth + 1 bits

            if (newID == old) { // If the tuple still in old bucket
                if (addToPage(replacePage, c) == -1) { // If current replacing page is full
                    // Replace the page
                    if (isReplaceOverflow) putPage(ovflowFile(r), curReplacePageID, replacePage);
                    else putPage(dataFile(r), curReplacePageID, replacePage);
                    npagesReplaced++; // We have replaced one page
                    isReplaceOverflow = 1;

                    replacePage = newPage(); // Create a new replacing page
                    // Update current replacing page id and next replacing page id
                    curReplacePageID = nextReplacePageID;
                    Page p = getPage(ovflowFile(r), curReplacePageID);
                    nextReplacePageID = pageOvflow(p);
                    free(p);
                    pageSetOvflow(replacePage, nextReplacePageID);

                    addToPage(replacePage, c); // Add this tuple to new distribution page
                }
            } else addTuple(r, new, c); // Else, the tuple go to new bucket, add it directly
            examinedTuples++; // This tuple examined

            // If there is more tuple remaining, update c to next tuple start
            c = examinedTuples < ntuples ? c + strlen(c) + 1 : c;
        }

        // All the tuples are examined, if current page is not overflow page, set is_overflow to 1
        isTraverseOverflow = 1;
        currentPageID = pageOvflow(oldPage); // Get next page id
        npages++; // We have examined one page
    }

    // Examine is finished, replace
    if (isReplaceOverflow) putPage(ovflowFile(r), curReplacePageID, replacePage);
    else putPage(dataFile(r), curReplacePageID, replacePage);
    npagesReplaced++;

    // If we haven't replaced all buckets, replace all unplaced buckets with empty page
    while (npagesReplaced < npages) {
        replacePage = newPage(); // Create a new replacing page
        curReplacePageID = nextReplacePageID;
        Page p = getPage(ovflowFile(r), curReplacePageID);
        nextReplacePageID = pageOvflow(p);
        free(p);
        pageSetOvflow(replacePage, nextReplacePageID);
        putPage(ovflowFile(r), curReplacePageID, replacePage);
        npagesReplaced++;
    }

}

Count relnPower(Count n) {
    Count res = 1;
    for (int i = 0; i < n; i++) {
        res *= 2;
    }
    return res;
}

void split(Reln r) {
    distributeTuples(r->sp, r);
    r->sp++;
    if (r->sp == relnPower(r->depth)) {
        r->depth++;
        r->sp = 0;
    }
}

// insert a new tuple into a relation
// returns index of bucket where inserted
// - index always refers to a primary data page
// - the actual insertion page may be either a data page or an overflow page
// returns NO_PAGE if insert fails completely

PageID addToRelation(Reln r, Tuple t)
{
    Count limit = PAGESIZE / (10 * nattrs(r));
    if (r->ntups != 0 && r->ntups % limit == 0) split(r);

	Bits h, p;
	h = tupleHash(r, t);
    char buf[MAXBITS + 4];
    bitsString(h, buf);
    printf("hash(%s) = %s\n", t, buf);
	if (r->depth == 0)
		p = 0;
	else {
		p = getLower(h, r->depth);
		if (p < r->sp) p = getLower(h, r->depth+1);
	}
	// bitsString(h,buf); printf("hash = %s\n",buf);
	// bitsString(p,buf); printf("page = %s\n",buf);
    PageID pid = addTuple(r, p, t);
    if (pid != NO_PAGE) r->ntups++;
    return pid;
}

// external interfaces for Reln data

FILE *dataFile(Reln r) { return r->data; }
FILE *ovflowFile(Reln r) { return r->ovflow; }
Count nattrs(Reln r) { return r->nattrs; }
Count npages(Reln r) { return r->npages; }
Count ntuples(Reln r) { return r->ntups; }
Count depth(Reln r)  { return r->depth; }
Count splitp(Reln r) { return r->sp; }
ChVecItem *chvec(Reln r)  { return r->cv; }


// displays info about open Reln

void relationStats(Reln r)
{
	printf("Global Info:\n");
	printf("#attrs:%d  #pages:%d  #tuples:%d  d:%d  sp:%d\n",
	       r->nattrs, r->npages, r->ntups, r->depth, r->sp);
	printf("Choice vector\n");
	printChVec(r->cv);
	printf("Bucket Info:\n");
	printf("%-4s %s\n","#","Info on pages in bucket");
	printf("%-4s %s\n","","(pageID,#tuples,freebytes,ovflow)");
	for (Offset pid = 0; pid < r->npages; pid++) {
		printf("[%2d]  ",pid);
		Page p = getPage(r->data, pid);
		Count ntups = pageNTuples(p);
		Count space = pageFreeSpace(p);
		Offset ovid = pageOvflow(p);
		printf("(d%d,%d,%d,%d)",pid,ntups,space,ovid);
		free(p);
		while (ovid != NO_PAGE) {
			Offset curid = ovid;
			p = getPage(r->ovflow, ovid);
			ntups = pageNTuples(p);
			space = pageFreeSpace(p);
			ovid = pageOvflow(p);
			printf(" -> (ov%d,%d,%d,%d)",curid,ntups,space,ovid);
			free(p);
		}
		putchar('\n');
	}
}
