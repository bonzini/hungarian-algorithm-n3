// -*- mode: c, coding: utf-8 -*-

/**
 * 𝓞(n³) implementation of the Hungarian algorithm
 * 
 * Copyright (C) 2011, 2014  Mattias Andrée
 * 
 * This program is free software. It comes without any warranty, to
 * the extent permitted by applicable law. You can redistribute it
 * and/or modify it under the terms of the Do What The Fuck You Want
 * To Public License, Version 2, as published by Sam Hocevar. See
 * http://sam.zoy.org/wtfpl/COPYING for more details.
 */


#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <limits.h>
#include <assert.h>


#ifndef RANDOM_DEVICE
#define RANDOM_DEVICE "/dev/urandom"
#endif


#define cell      long
#define CELL_MAX  LONG_MAX
#define CELL_STR  "%li"

typedef uintptr_t llong;
typedef int_fast8_t byte;
typedef unsigned char boolean;
#define TRUE     1
#define FALSE    0



#ifdef DEBUG
#  define debug(X) fprintf(stderr, "\033[31m%s\033[m\n", X)
#else
#  define debug(X) 
#endif




/**
 * Cell marking:  none
 */
#define UNMARKED  0L

/**
 * Cell marking:  marked
 */
#define MARKED    1L

/**
 * Cell marking:  prime
 */
#define PRIME     2L



/**
 * Bit set, a set of fixed number of bits/booleans
 */
typedef struct
{
    /**
     * The set of all limbs, a limb consist of 64 bits
     */
    llong* limbs;
    
    /**
     * Index of the first non-zero limb
     */
    ssize_t first;
    
    /**
     * Array the the index of the previous non-zero limb for each limb
     */
    ssize_t* prev;
    
    /**
     * Array the the index of the next non-zero limb for each limb
     */
    ssize_t* next;
    
} BitSet;



ssize_t** kuhn_match(cell** table, size_t n, size_t m);
static void kuhn_reduceRows(cell** t, size_t n, size_t m);
static size_t kuhn_markZeroes(cell** t, byte** marks, boolean* colCovered, size_t n, size_t m);
static size_t kuhn_markColumns(byte** marks, boolean* colCovered, size_t n, size_t m);
static boolean kuhn_findPrime(cell** t, byte** marks, boolean* rowCovered, boolean* colCovered, size_t* primeRow, size_t* primeCol, size_t n, size_t m);
static void kuhn_altMarks(byte** marks, ssize_t currRow, ssize_t currCol, ssize_t* colMarks, ssize_t* rowPrimes, size_t n, size_t m);
static void kuhn_addAndSubtract(cell** t, boolean* rowCovered, boolean* colCovered, size_t n, size_t m);
static ssize_t** kuhn_assign(byte** marks, size_t n, size_t m);

static void BitSet_init(BitSet *this, size_t size);
static void BitSet_free(BitSet *this);
static void BitSet_set(BitSet *this, size_t i);
static void BitSet_unset(BitSet *this, size_t i);
static ssize_t BitSet_any(BitSet *this) __attribute__((pure));

static size_t lb(llong x) __attribute__((const));



void print(cell** t, size_t n, size_t m, ssize_t** assignment);

int main(int argc, char** argv)
{
    size_t i, j;
    size_t n, m;
    if (argc >= 3)
    {
        n = atol(argv[1]);
        m = atol(argv[2]);
        unsigned int seed;
        if (argc == 3) {
            FILE* urandom = fopen(RANDOM_DEVICE, "r");
            fread(&seed, sizeof(unsigned int), 1, urandom);
            fclose(urandom);
        } else {
            seed = atoi(argv[3]);
        }
        printf("seed: %u\n\n", seed);
        srand(seed);
    } else {
        if (scanf(CELL_STR, &n) != 1) exit(1);
        if (scanf(CELL_STR, &m) != 1) exit(1);
    }
    cell** t = malloc(n * sizeof(cell*));
    cell** table = malloc(n * sizeof(cell*));
    if (argc >= 3) {
        for (i = 0; i < n; i++) {
	    t[i] = malloc(m * sizeof(cell));
	    table[i] = malloc(m * sizeof(cell));
	    for (j = 0; j < m; j++)
	        table[i][j] = t[i][j] = (cell)(random() & 63);
	}
    } else {
        for (i = 0; i < n; i++) {
	    t[i] = malloc(m * sizeof(cell));
	    table[i] = malloc(m * sizeof(cell));
	    for (j = 0; j < m; j++) {
                cell x;
                if (scanf(CELL_STR, &x) != 1) exit(1);
	        table[i][j] = t[i][j] = x;
	    }
	}
    }
    
    printf("\nInput:\n\n");
    print(t, n, m, NULL);
    
    ssize_t** assignment = kuhn_match(table, n, m);
    printf("\nOutput:\n\n");
    print(t, n, m, assignment);
    
    cell sum = 0;
    for (i = 0; i < n; i++) {
        sum += t[assignment[i][0]][assignment[i][1]];
	free(assignment[i]);
	free(table[i]);
	free(t[i]);
    }
    free(assignment);
    free(table);
    free(t);
    printf("\n\nSum: %li\n\n", sum);
    
    return 0;
}

void print(cell** t, size_t n, size_t m, ssize_t** assignment)
{
    size_t i, j;
    
    ssize_t** assigned = malloc(n * sizeof(ssize_t*));
    for (i = 0; i < n; i++) {
        assigned[i] = malloc(m * sizeof(ssize_t));
	for (j = 0; j < m; j++)
	    assigned[i][j] = 0;
    }
    if (assignment != NULL)
        for (i = 0; i < n; i++)
	    assigned[assignment[i][0]][assignment[i][1]]++;
    
    for (i = 0; i < n; i++) {
	printf("    ");
	for (j = 0; j < m; j++) {
	    if (assigned[i][j])
	      printf("\033[%im", (int)(30 + assigned[i][j]));
	    printf("%5li%s\033[m   ", (cell)(t[i][j]), (assigned[i][j] ? "^" : " "));
        }
	printf("\n\n");
	
	free(assigned[i]);
    }
    
    free(assigned);
}



/**
 * Calculates an optimal bipartite minimum weight matching using an
 * O(n³)-time implementation of The Hungarian Algorithm, also known
 * as Kuhn's Algorithm.
 * 
 * @param   table  The table in which to perform the matching
 * @param   n      The height of the table
 * @param   m      The width of the table
 * @return         The optimal assignment, an array of row–coloumn pairs
 */
ssize_t** kuhn_match(cell** table, size_t n, size_t m)
{
    size_t i;
    
    /* not copying table since it will only be used once */
    
    ssize_t* rowPrimes = malloc(n * sizeof(ssize_t));
    ssize_t* colMarks  = malloc(m * sizeof(ssize_t));

    boolean* rowCovered = calloc(n, sizeof(boolean));
    boolean* colCovered = calloc(m, sizeof(boolean));
    
    byte** marks = malloc(n * sizeof(byte*));
    for (i = 0; i < n; i++)
        marks[i] = calloc(m, sizeof(byte));
    
    kuhn_reduceRows(table, n, m);
    if (kuhn_markZeroes(table, marks, colCovered, n, m) < n) {
        do {
            size_t primeRow, primeCol;
            while (!kuhn_findPrime(table, marks, rowCovered, colCovered, &primeRow, &primeCol, n, m))
	        kuhn_addAndSubtract(table, rowCovered, colCovered, n, m);

	    kuhn_altMarks(marks, primeRow, primeCol, colMarks, rowPrimes, n, m);
        } while (kuhn_markColumns(marks, colCovered, n, m) < n);
    }
    
    free(rowCovered);
    free(colCovered);
    free(rowPrimes);
    free(colMarks);
    
    ssize_t** rc = kuhn_assign(marks, n, m);
    
    for (i = 0; i < n; i++)
        free(marks[i]);
    free(marks);
    
    return rc;
}


/**
 * Reduces the values on each rows so that, for each row, the
 * lowest cells value is zero, and all cells' values is decrease
 * with the same value [the minium value in the row].
 * 
 * @param  t  The table in which to perform the reduction
 * @param  n  The table's height
 * @param  m  The table's width
 */
void kuhn_reduceRows(cell** t, size_t n, size_t m)
{
    size_t i, j;
    cell min;
    cell* ti;
    for (i = 0; i < n; i++) {
        ti = t[i];
        min = ti[0];
	for (j = 1; j < m; j++)
	    if (min > ti[j])
	        min = ti[j];
	
	for (j = 0; j < m; j++)
	    ti[j] -= min;
    }
}


/**
 * Fill a matrix with marking of cells in the table whose
 * value is zero [minimal for the row]. Each marking will
 * be on an unique row and an unique column.
 * 
 * @param   t  The table in which to perform the reduction
 * @param   marks       The marking matrix
 * @param   colCovered  An array which tells whether a column is covered
 * @param   n  The table's height
 * @param   m  The table's width
 * @return  The number of covered columns
 */
size_t kuhn_markZeroes(cell** t, byte **marks, boolean *colCovered, size_t n, size_t m)
{
    size_t i, j;
    size_t count = 0;

    for (i = 0; i < n; i++)
        for (j = 0; j < m; j++)
	    if (!colCovered[j] && t[i][j] == 0) {
	        marks[i][j] = MARKED;
		colCovered[j] = TRUE;
                count++;
                break;
	    }

    return count;
}


/**
 * Determines whether the marking is complete, that is
 * if each row has a marking which is on a unique column.
 * Find covered columns while at it.
 *
 * @param   marks       The marking matrix
 * @param   colCovered  An array which tells whether a column is covered
 * @param   n           The table's height
 * @param   m           The table's width
 * @return              Number of rows with a mark
 */
size_t kuhn_markColumns(byte** marks, boolean* colCovered, size_t n, size_t m)
{
    size_t i, j;
    size_t count = 0;

    memset(colCovered, 0, m);
    for (i = 0; i < n; i++)
        for (j = 0; j < m; j++)
	    if (!colCovered[j] && marks[i][j] == MARKED) {
	        colCovered[j] = TRUE;
                count++;
		break;
	    }
    
    return count;
}


/**
 * Finds a prime
 * 
 * @param   t           The table
 * @param   marks       The marking matrix
 * @param   rowCovered  Row cover array
 * @param   colCovered  Column cover array
 * @param   n           The table's height
 * @param   m           The table's width
 * @return              The row and column of the found print, <code>NULL</code> will be returned if none can be found
 */
boolean kuhn_findPrime(cell** t, byte** marks, boolean* rowCovered, boolean* colCovered, size_t* primeRow, size_t* primeCol, size_t n, size_t m)
{
    size_t i, j;
    size_t row, col;
    BitSet zeroes;
   
    BitSet_init(&zeroes, n * m);
    
    for (i = 0; i < n; i++)
	for (j = 0; j < m; j++)
	    if (!colCovered[j] && t[i][j] == 0)
		BitSet_set(&zeroes, i * m + j);

    memset(rowCovered, 0, n);
    for (;;) {
        ssize_t p = BitSet_any(&zeroes);
	if (p < 0) {
	    BitSet_free(&zeroes);
	    return FALSE;
	}
	
	row = (size_t)p / m;
	col = (size_t)p % m;
	
	marks[row][col] = PRIME;
	
	for (j = 0; j < m; j++)
	    if (marks[row][j] == MARKED) {
		col = j;
                break;
	    }
	
	if (j == m)
            break;

	BitSet_unset(&zeroes, p);
	rowCovered[row] = TRUE;
	colCovered[col] = FALSE;
	
	for (i = 0; i < n; i++)
	    if (row != i && t[i][col] == 0) {
	        if (!rowCovered[i])
	            BitSet_set(&zeroes, i * m + col);
	        else
	            BitSet_unset(&zeroes, i * m + col);
	    }
	
	for (j = 0; j < m; j++)
	    if (col != j && t[row][j] == 0)
	        BitSet_unset(&zeroes, row * m + j);
	
    }

    *primeRow = row;
    *primeCol = col;
    BitSet_free(&zeroes);
    return TRUE;
}


static inline void kuhn_altMark(byte **marks, ssize_t currRow, ssize_t currCol)
{
    if (marks[currRow][currCol] == MARKED)
        marks[currRow][currCol] = UNMARKED;
    else
        marks[currRow][currCol] = MARKED;
}

/**
 * Removes all prime marks and modifies the marking
 *
 * @param  marks      The marking matrix
 * @param  altRow     Marking modification path rows
 * @param  altCol     Marking modification path columns
 * @param  colMarks   Markings in the columns
 * @param  rowPrimes  Primes in the rows
 * @param  prime      The last found prime
 * @param  n          The table's height
 * @param  m          The table's width
 */
void kuhn_altMarks(byte** marks, ssize_t currRow, ssize_t currCol, ssize_t* colMarks, ssize_t* rowPrimes, size_t n, size_t m)
{
    size_t index = 0, i, j;
    
    for (i = 0; i < n; i++)
        rowPrimes[i] = -1;
    for (j = 0; j < m; j++)
        colMarks[j] = -1;
    
    for (i = 0; i < n; i++)
        for (j = 0; j < m; j++)
	    if (marks[i][j] == MARKED)
	        colMarks[j] = (ssize_t)i;
	    else if (marks[i][j] == PRIME)
	        rowPrimes[i] = (ssize_t)j;
    
    kuhn_altMark(marks, currRow, currCol);
    for (;;) {
        currRow = colMarks[currCol];
	if (currRow < 0)
	    break;
        kuhn_altMark(marks, currRow, currCol);
	
	currCol = rowPrimes[currRow];
        assert(currCol >= 0);
        kuhn_altMark(marks, currRow, currCol);
    }
    
    for (i = 0; i < n; i++) {
        byte *marksi = marks[i];
        for (j = 0; j < m; j++)
	    if (marksi[j] == PRIME)
	        marksi[j] = UNMARKED;
    }
}


/**
 * Depending on whether the cells' rows and columns are covered,
 * the the minimum value in the table is added, subtracted or
 * neither from the cells.
 *
 * @param  t           The table to manipulate
 * @param  rowCovered  Array that tell whether the rows are covered
 * @param  colCovered  Array that tell whether the columns are covered
 * @param  n           The table's height
 * @param  m           The table's width
 */
void kuhn_addAndSubtract(cell** t, boolean* rowCovered, boolean* colCovered, size_t n, size_t m)
{
    size_t i, j;
    cell min = CELL_MAX;
    for (i = 0; i < n; i++)
        if (!rowCovered[i])
	    for (j = 0; j < m; j++)
	        if (!colCovered[j] && min > t[i][j])
		    min = t[i][j];

    for (i = 0; i < n; i++) {
        for (j = 0; j < m; j++) {
	    if (rowCovered[i])
	        t[i][j] += min;
	    if (!colCovered[j])
	        t[i][j] -= min;
	}
    }
}


/**
 * Creates a list of the assignment cells
 * 
 * @param   marks  Matrix markings
 * @param   n      The table's height
 * @param   m      The table's width
 * @return         The assignment, an array of row–coloumn pairs
 */
ssize_t** kuhn_assign(byte** marks, size_t n, size_t m)
{
    ssize_t** assignment = malloc(n * sizeof(ssize_t*));
    
    size_t i, j;
    for (i = 0; i < n; i++) {
        assignment[i] = malloc(2 * sizeof(ssize_t));
        for (j = 0; j < m; j++)
	    if (marks[i][j] == MARKED) {
		assignment[i][0] = (ssize_t)i;
		assignment[i][1] = (ssize_t)j;
	    }
    }
    
    return assignment;
}


/**
 * Constructor for BitSet
 *
 * @param   size  The (fixed) number of bits to bit set should contain
 * @return        The a unique BitSet instance with the specified size
 */
void BitSet_init(BitSet *this, size_t size)
{
    size_t c = size >> 6L;
    if (size & 63L)
        c++;
    
    this->limbs = calloc(c, sizeof(llong));
    this->prev = calloc(c, sizeof(size_t));
    this->next = calloc(c, sizeof(size_t));
    this->first = -1;
}

void BitSet_free(BitSet *this)
{
    free(this->limbs);
    free(this->prev);
    free(this->next);
}

/**
 * Turns on a bit in a bit set
 * 
 * @param  this  The bit set
 * @param  i     The index of the bit to turn on
 */
void BitSet_set(BitSet *this, size_t i)
{
    size_t j = i >> 6L;
    llong old = this->limbs[j];
    
    this->limbs[j] |= 1LL << (llong)(i & 63L);
    
    if (!old) {
        if (this->first != -1)
	    this->prev[this->first] = j;
	this->prev[j] = -1;
	this->next[j] = this->first;
	this->first = j;
    }
}

/**
 * Turns off a bit in a bit set
 * 
 * @param  this  The bit set
 * @param  i     The index of the bit to turn off
 */
void BitSet_unset(BitSet *this, size_t i)
{
    size_t j = i >> 6L;
    llong old = this->limbs[j];
    
    if (!old)
        return;

    this->limbs[j] &= ~(1LL << (llong)(i & 63L));
    
    if (!this->limbs[j]) {
	size_t p = this->prev[j];
	size_t n = this->next[j];
        if (n != -1)
	    this->prev[n] = p;
        if (p == -1)
	    this->first = n;
        else
	    this->next[p] = n;
    }
}

/**
 * Gets the index of any set bit in a bit set
 * 
 * @param   this  The bit set
 * @return        The index of any set bit
 */
ssize_t BitSet_any(BitSet *this)
{
    ssize_t i = this->first;
    if (i == -1)
        return -1;
    
    return (ssize_t)(lb(this->limbs[i] & -this->limbs[i]) + (i << 6L));
}


/**
 * Calculates the floored binary logarithm of a positive integer
 *
 * @param   value  The integer whose logarithm to calculate
 * @return         The floored binary logarithm of the integer
 */
size_t lb(llong value)
{
    size_t rc = 0;
    llong v = value;
    
    if (v & (int_fast64_t)0xFFFFFFFF00000000LL)  {  rc |= 32L;  v >>= 32LL;  }
    if (v & (int_fast64_t)0x00000000FFFF0000LL)  {  rc |= 16L;  v >>= 16LL;  }
    if (v & (int_fast64_t)0x000000000000FF00LL)  {  rc |=  8L;  v >>=  8LL;  }
    if (v & (int_fast64_t)0x00000000000000F0LL)  {  rc |=  4L;  v >>=  4LL;  }
    if (v & (int_fast64_t)0x000000000000000CLL)  {  rc |=  2L;  v >>=  2LL;  }
    if (v & (int_fast64_t)0x0000000000000002LL)     rc |=  1L;
    
    return rc;
}

