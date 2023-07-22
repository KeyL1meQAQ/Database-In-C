// query.c ... query scan functions
// part of Multi-attribute Linear-hashed Files
// Manage creating and using Query objects
// Last modified by John Shepherd, July 2019

#include "defs.h"
#include "query.h"
#include "reln.h"
#include "tuple.h"
#include "hash.h"

// A suggestion ... you can change however you like

struct QueryRep {
	Reln    rel;       // need to remember Relation info
	Bits    known;     // the hash value from MAH
	Bits    unknown;   // the unknown bits from MAH
	PageID  curpage;   // current page in scan
    PageID prevpage;   // previous main page
	int     is_ovflow; // are we in the overflow pages?
	Offset  curtup;    // offset of current tuple within page
    int *unknownIndex; // The index(position) of all unknown bits
    Count nunknowns; // How many unknown bits
    Bits curCover; // The current cover on unknown bits
    Count examinedTuples; // How many tuples in current page has been examined
    char *query;
};

// take a query string (e.g. "1234,?,abc,?")
// set up a QueryRep object for the scan

int validQuery(Reln r, char *q) {
    int nvals = 1;
    for (char *c = q; *c != '\0'; c++) {
        if (*c == ',') {
            nvals++;
        }
    }
    int relationAttrs = nattrs(r);
    if (nvals != relationAttrs) {
        return 0;
    }
    return 1;
}

Count power(Count n) {
    Count res = 1;
    for (int i = 0; i < n; i++) {
        res *= 2;
    }
    return res;
}

PageID getNextPageID(Bits cover, Bits known, Bits unknown, Count nunknowns, int *unknownIndex, Reln r) {
    Bits curUnknown = unknown;
    for (int i = 0; i < nunknowns; i++) {
        curUnknown = bitIsSet(cover, i) ? setBit(curUnknown, unknownIndex[i]) : unsetBit(curUnknown, unknownIndex[i]);
    }
    Count sp = splitp(r);
    int relationDepth = depth(r);
    PageID pid = known | curUnknown;
    pid = getLower(pid, relationDepth) < sp ? getLower(pid, relationDepth + 1) : getLower(pid, relationDepth);
    if (pid >= npages(r)) return NO_PAGE; // If next page id is not exist
    return pid;
}

Query startQuery(Reln r, char *q)
{
	Query new = malloc(sizeof(struct QueryRep));
	assert(new != NULL);

    if (!validQuery(r, q)) return NULL;

    Count relationDepth = depth(r);
    Count nvals = nattrs(r);
    ChVecItem *chVec = chvec(r);
    char **vals = malloc(nvals * sizeof(char *));
    assert(vals != NULL);
    tupleVals(q, vals);

    // form known bits from known attributes
    // form unknown bits from '?' attributes
    Bits known = 0;
    Bits unknown = 0;
    int *unknownIndex = malloc(MAXBITS * sizeof (int ));
    assert(unknownIndex != NULL);
    Count nunknowns = 0;
    for (int i = 0; i < relationDepth + 1; i++) {
        int attrIndex = chVec[i].att;
        int positionIndex = chVec[i].bit;
        if (strcmp(vals[attrIndex], "?") != 0) {
            Bits hash = hash_any((unsigned char *)vals[attrIndex], strlen(vals[attrIndex]));
            known = bitIsSet(hash, positionIndex) ? setBit(known, i) : unsetBit(known, i);
        } else {
            unknown = setBit(unknown, i);
            unknownIndex[nunknowns] = i;
            nunknowns++;
        }
    }

    char buf1[MAXBITS + 1];
    char buf2[MAXBITS + 1];
    bitsString(known, buf1);
    bitsString(unknown, buf2);


    freeVals(vals, nvals);

    // compute PageID of first page
    //   using known bits and first "unknown" value
    Bits cover = 0; // The first cover is always 0, cover would add 1 when we need to find next page id.
    PageID firstPage = getNextPageID(cover, known, unknown, nunknowns, unknownIndex, r);

	// set all values in QueryRep object
    new->rel = r;
    new->known = known;
    new->unknown = unknown;
    new->curpage = firstPage;
    new->prevpage = firstPage;
    new->is_ovflow = 0;
    new->curtup = 0;
    new->unknownIndex = unknownIndex;
    new->nunknowns = nunknowns;
    new->curCover = cover;
    new->examinedTuples = 0;
    new->query = q;
	return new;
}

// Find match tuple in a given page for a given query

Tuple findMatchTuple(Page p, Query q) {
    char *c = pageData(p) + q->curtup;
    while (pageNTuples(p) > q->examinedTuples) {
        if (tupleMatch(q->rel, c, q->query)) {
            q->examinedTuples++;
            q->curtup = pageNTuples(p) > q->examinedTuples ? q->curtup + strlen(c) + 1 : 0;
            return c;
        } else {
            q->examinedTuples++;
            if (pageNTuples(p) > q->examinedTuples) {
                q->curtup += (strlen(c) + 1);
                c += (strlen(c) + 1);
            } else q->curtup = 0;
        }
    }
    return NULL;
}

// get next tuple during a scan

Tuple getNextTuple(Query q)
{
    static Page p = NULL;

    while (1) { // loop until a match tuple is found, or all pages are examined
        // Get current page. Note the current page possibly has been fully examined
        // But still get it, to go into the branch of else if and else
        if (p == NULL) {
            p = q->is_ovflow ? getPage(ovflowFile(q->rel), q->curpage) : getPage(dataFile(q->rel), q->curpage);
        }

        if (pageNTuples(p) > q->examinedTuples) { // if (more tuples in current page)
            Tuple t = findMatchTuple(p, q); // Find a match tuple
            if (t != NULL) return t; // Found a match tuple, return this tuple, loop break
        } else { // If this page is fully examined (No more tuples)
            q->examinedTuples = 0;
            q->curtup = 0;
            PageID ovflowPageID = pageOvflow(p);
            free(p); // Free the memory of current page, which is fully examined
            if (ovflowPageID != NO_PAGE) { // else if (current page has overflow)
                q->is_ovflow = 1; // Now we are in overflow pages
                q->curpage = ovflowPageID; // Move to overflow page
            } else { // else, there is no overflow files anymore, so this page and all its overflow pages are examined
                // If this is the final page, return NULL, loop break and end the query
                if (q->curCover >= power(q->nunknowns) - 1) return NULL;
                q->curCover++;
                q->is_ovflow = 0;
                // Get next page id
                q->curpage = getNextPageID(q->curCover, q->known, q->unknown,
                                           q->nunknowns, q->unknownIndex, q->rel);
                // If next page id not exist, then every available pages are examined
                if (q->curpage == NO_PAGE || q->curpage <= q->prevpage) return NULL;
                q->prevpage = q->curpage;
            }
            p = q->is_ovflow ? getPage(ovflowFile(q->rel), q->curpage) : getPage(dataFile(q->rel), q->curpage);
        }
    }
}

// clean up a QueryRep object and associated data

void closeQuery(Query q)
{
    free(q->unknownIndex);
    free(q);
}
