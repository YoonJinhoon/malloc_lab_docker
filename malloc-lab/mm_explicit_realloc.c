/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 기본 단위 상수
#define WSIZE       4       
#define DSIZE       8
#define CHUNKSIZE   (1 << 12)

#define MAX(x, y)  ((x) > (y) ? (x) : (y))

#define PACK(size, alloc)  ((size) | (alloc))

#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp)   ( (char *)(bp) + GET_SIZE( ( (char *)(bp) - WSIZE ) ) )
#define PREV_BLKP(bp)   ( (char *)(bp) - GET_SIZE( ( (char *)(bp) - DSIZE ) ) )

#define PREC_P(bp)  ((void *)(bp))
#define SUCC_P(bp)  ((void *)((char *)(bp) + DSIZE))

#define GET_PREC(bp) (*(void **)(PREC_P(bp)))
#define GET_SUCC(bp) (*(void **)(SUCC_P(bp)))

#define SET_PREC(bp, prev) (*(void **)(PREC_P(bp)) = (void *)(prev))
#define SET_SUCC(bp, next) (*(void **)(SUCC_P(bp)) = (void *)(next))

static char *heap_listp = 0;
static void *free_listp = NULL;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static void insert_block(void *bp);
static void remove_block(void *bp);

static void insert_block(void *bp)
{
    SET_SUCC(bp, free_listp);
    SET_PREC(bp, NULL);

    if (free_listp != NULL) {
        SET_PREC(free_listp, bp);
    }
    free_listp = bp;
}

static void remove_block(void *bp)
{
    if (GET_PREC(bp) != NULL) {
        SET_SUCC(GET_PREC(bp), GET_SUCC(bp));
    } else {
        free_listp = GET_SUCC(bp);
    }

    if (GET_SUCC(bp) != NULL) {
        SET_PREC(GET_SUCC(bp), GET_PREC(bp));
    }
}

int mm_init(void)
{
    free_listp = NULL;

    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));

    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

static void*extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {

    }

    else if (prev_alloc && !next_alloc) {
        remove_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    
    else if (!prev_alloc && next_alloc) {
        remove_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {
        remove_block(PREV_BLKP(bp));
        remove_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    insert_block(bp);

    return bp;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 3 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = (asize > CHUNKSIZE) ? asize : CHUNKSIZE;
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize)
{
    void *bp;

    for (bp = free_listp; bp != NULL; bp = GET_SUCC(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }

    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    remove_block(bp);

    if ((csize - asize) >= (3 * DSIZE)) {

        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));

        insert_block(bp);
    }

    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    size_t new_asize;
    if (size <= 2 * DSIZE)
        new_asize = 3 * DSIZE;
    else
        new_asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    size_t old_size = GET_SIZE(HDRP(ptr));

    if (old_size >= new_asize) {
        return ptr;
    }

    void *next_bp = NEXT_BLKP(ptr);
    size_t combined_size = old_size + GET_SIZE(HDRP(next_bp));

    if (!GET_ALLOC(HDRP(next_bp)) && (combined_size >= new_asize)) {
        remove_block(next_bp);

        if (combined_size - new_asize >= 3 * DSIZE) {
            PUT(HDRP(ptr), PACK(new_asize, 1));
            PUT(FTRP(ptr), PACK(new_asize, 1));

            void *remainder_bp = NEXT_BLKP(ptr);
            PUT(HDRP(remainder_bp), PACK(combined_size - new_asize, 0));
            PUT(FTRP(remainder_bp), PACK(combined_size - new_asize, 0));
            insert_block(remainder_bp);
        } else {
            PUT(HDRP(ptr), PACK(combined_size, 1));
            PUT(FTRP(ptr), PACK(combined_size, 1));
        }

        return ptr;
    }

    void *new_ptr = mm_malloc(size);
    if (new_ptr == NULL)
        return NULL;

    size_t copy_size = old_size - DSIZE;
    if (size < copy_size)
        copy_size = size;

    memcpy(new_ptr, ptr, copy_size);
    mm_free(ptr);

    return new_ptr;
}