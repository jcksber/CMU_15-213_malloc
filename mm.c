/*
 * mm.c
 *
 * Jack Kasbeer (jkasbeer)
 * July 14, 2015
 *
 * Dynamic memory allocator: 32-bit and 64-bit clean allocator based on SEGREGATED fit
 * lists, LIFO free block ordering, FIRST FIT placement, and boundary tag coalescing, 
 * as described in the CS:APP2e text. 
 * Blocks must be aligned to doubleword (8 byte) 
 * boundaries. 
 * Minimum block size is 24 bytes. 
 *
 * 
 */

/* BLOCK INFO -- 
 * Block:  F [ HDR | NEXTP | PREVP | FTR ] 
 *         A [ HDR |    PAYLOADS   | FTR ]
 * Bytes:      4      8        8      4   ==> MIN_BLK_SIZE = 24 bytes
 */

#include <assert.h>
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

typedef unsigned int u_int;
typedef unsigned long long u_llong;

/* Single word (4) aligned or double word (8) aligned */
#define ALIGNMENT     8 /* DSIZE alignment for 64-bit machines */

/* ## GENERAL MACROS ## */

/* Basic constants and macros */
#define WSIZE         4       /* Word and header/footer size (bytes) */
#define DSIZE         8       /* Doubleword size (bytes) */
#define OVERHEAD      8       /* Needed for prologue alignment */
#define MIN_BLK_SIZE 24       /* next & prev ptr's 8 bytes for 64-bit */
#define INITSIZE     (1<<6)   /* chunksize specific to mm_init */
#define CHUNKSIZE    (1<<11)  /* Extend heap by this amount (bytes) */

/* Determine larger variable, given two */
#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)           (*(u_int *)(p))
#define PUT(p, val)      (*(u_int *)(p) = (val))
#define PUT_WTAG(p, val) (*(u_int *)(p) = (val) | GET_TAG(p))

/* Read the size and allocated fields from address p */ 
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Read the free block's reallocation tag */
#define GET_TAG(p)   (GET(p) & 0x2)

/* Set/remove the free block's reallocation tag */
#define SET_TAG(p)   (GET(p) |= 0x2) // in realloc
#define REMOVE_TAG(p) (GET(p) &= ~0x2)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ( (char *)(bp) - WSIZE )
#define FTRP(bp)       ( (char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE ) 

/* Given block ptr bp, compute address of next & previous blocks */
#define NEXT_BLKP(bp)  ( (char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)) )
#define PREV_BLKP(bp)  ( (char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)) )

/* ## EXPLICIT FREE LIST MACROS ## */

/* Compute address of next & prev free block entries */
#define NEXT_FREEP(bp) ( *(char **)bp )
#define PREV_FREEP(bp) ( *(char **)(bp + DSIZE) )

/* ## SEGREGATED LIST MACROS ## */

#define NUM_LISTS  10 /* supports 16 - 16,376 byte free blocks */
#define SLIST0   16   /* seglist[0] */ 
#define SLIST1   32   /* seglist[1] */ 
#define SLIST2   64   /* seglist[2] */ 
#define SLIST3  128   /* seglist[3] */ 
#define SLIST4  256   /* seglist[4] */ 
#define SLIST5  512   /* seglist[5] */ 
#define SLIST6 1024   /* seglist[6] */ 
#define SLIST7 2048   /* seglist[7] */ 
#define SLIST8 4096   /* seglist[8] */ 
#define SLIST9 8192   /* seglist[9] */ 

/* Global variables */
static char *heap_listp = 0; /* Pointer to first block */
void *seglist[NUM_LISTS];    /* Array of size classe ptr's for segregated list:
                              * element i points to the start of the size class
                              * 2^(i+4), containing up to 2^(i+1+4) bytes
                              * (for 0 <= i <= 9)
                              */
/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);     
static void *find_fit(size_t asize);
static void place(void *ptr, size_t asize);         
static void *coalesce(void *ptr);
static int  seg_search(size_t asize);
static void *seg_fit(int bucket, size_t size);
static void seg_insertb(void *fp, size_t fsize);
static void seg_removeb(void *fp, size_t fsize);
/* Function prototypes for debugging routines */
static void mylistcheck();
static void printfree(void *fp);   
static void printb(void *bp);       
static void checkb(void *bp);      
static int in_heap(const void *p);
static int aligned(const void *p);  


/******************************
 * DYNAMIC MEMORY ALLOCATOR PKG
 ******************************/

/*
 * mm_init - initialize an empty heap: return -1 on error, 0 on success.
 */
int mm_init(void) 
{
  int i;
  /* Initialize segregated free lists */
  for (i = 0; i < NUM_LISTS; i++)
    seglist[i] = NULL;

  /* Check for error then initialize empty heap */
  if (!(heap_listp = mem_sbrk(4*WSIZE)))  return -1;

  /* Set up the heap with padding, prologue, and epilogue */
  PUT(heap_listp, 0);                          /* Alignment padding */
  PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
  PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
  PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (!extend_heap(INITSIZE))  return -1; 

  return 0;
}

/*
 * malloc - memory allocation.. allocate requested size (bytes)
 */
void *malloc(size_t size) 
{
  size_t asize;      /* Adjusted block size */
  size_t extendsize; /* Amount to extend heap if no fit */
  char *bp;      

  /* Specific case checks -- */
  // First call to malloc
  if (!heap_listp) mm_init();
  // Trivial call to malloc
  if (!size) return NULL;

  /* Determine size to allocate -- */
  asize = MAX( ALIGN(size) + OVERHEAD, MIN_BLK_SIZE );

  /* Search for a fit.. */
  bp = find_fit(asize);
  /* No fit found ==> need more heap! */
  if (!bp) {
    extendsize = MAX(asize, CHUNKSIZE) / WSIZE;
    if (!(bp = extend_heap(extendsize)))  return NULL;
  }

  /* Allocate space in memory before returning ptr */
  place(bp, asize);
  return bp;
}

/*
 * free - free block of memory starting at bp
 */
void free(void *bp)
{
  /* Specific case checks -- */
  if (!bp) return;
  if (!heap_listp) mm_init();

  size_t size = GET_SIZE(HDRP(bp));

  REMOVE_TAG(HDRP(NEXT_BLKP(bp))); // for realloc
  PUT_WTAG(HDRP(bp), PACK(size, 0));
  PUT_WTAG(FTRP(bp), PACK(size, 0));

  /* Coalesce adjacent blocks then add block to free list */
  coalesce(bp);
}

/*
 * coalesce - Coalesce adjacent free blocks (if any), 
 *            add coalesced block to free list,
 *            and return ptr to block.
 */
static void *coalesce(void *bp) 
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc)              /* Case 1 */
    bp = bp; /* don't do anything to block */
  else if (prev_alloc && !next_alloc) {      /* Case 2 */
    /* Adjust size for new free block */
    size_t nsize = GET_SIZE(HDRP(NEXT_BLKP(bp)));
    size += nsize;
    /* Remove adjacent free block */
    seg_removeb(NEXT_BLKP(bp), nsize);
    /* Adjust header & footer of new free block */
    PUT_WTAG(HDRP(bp), PACK(size, 0));       
    PUT_WTAG(FTRP(bp), PACK(size, 0));              
  }
  else if (!prev_alloc && next_alloc) {      /* Case 3 */
    /* Adjust size for new free block */
    size_t psize = GET_SIZE(HDRP(PREV_BLKP(bp)));
    size += psize;
    /* Remove adjacent free block */
    seg_removeb(PREV_BLKP(bp), psize);
    /* Adjust header & footer of new free block */
    bp = PREV_BLKP(bp); /* adjust bp for insertion */
    PUT_WTAG(HDRP(bp), PACK(size, 0));
    PUT_WTAG(FTRP(bp), PACK(size, 0)); 
  }
  else {                                     /* Case 4 */
    /* Adjust size for new free block */
    size_t nsize = GET_SIZE(HDRP(NEXT_BLKP(bp)));
    size_t psize = GET_SIZE(HDRP(PREV_BLKP(bp)));
    size += nsize + psize;
    /* Remove adjacent free blocks */
    seg_removeb(NEXT_BLKP(bp), nsize);
    /* Adjust header & footer of new free block */
    bp = PREV_BLKP(bp); /* adjust bp for insertion */
    seg_removeb(bp, psize);
    PUT_WTAG(HDRP(bp), PACK(size, 0));
    PUT_WTAG(FTRP(bp), PACK(size, 0));
  }
  /* Insert new free block into appropriate list */
  seg_insertb(bp, size);

  return bp;
}

/*
 * seg_search - determine the proper segregated list to use based on size;
 *              return index for the appropriate bucket
 */
static int seg_search(size_t size)
{
  /* Search for the appropriate SLIST# & return index for seglist[] */
  if (size < SLIST5) {    /* SLIST 0,1,2,3,4 */
    if (size < SLIST2) {  
      return (size <= SLIST1 ? 0 : 1);
    }
    else if (size < SLIST4)
      return (size <= SLIST3 ? 2 : 3);
    else
      return 4;
  }
  else {                  /* SLIST 5,6,7,8,9 */
    if (size < SLIST7) {  
      return (size <= SLIST6 ? 5 : 6);
    }
    else if (size < SLIST9)
      return (size <= SLIST8 ? 7 : 8);
    else
      return 9;
  }
}

/*
 * seg_insertb - insert a free block into the appropriate
 *               segregated list based on its size
 */
static void seg_insertb(void *fp, size_t fsize)
{
  /* Select segregated list */
  int bucket = seg_search(fsize);

  /* Search segregated list for fit */
  char *listp;
  while ( ((listp = seg_fit(bucket, fsize)) == NULL) && (bucket < (NUM_LISTS-1)) )
        { bucket++; } /* increment bucket every time fit not found */

  /* Insert block */
  if (listp) {
    /* previous segregated list start now needs prev ptr */
    PREV_FREEP(listp) = fp; 
    /* set next free ptr to old start of list */
    NEXT_FREEP(fp) = listp; 
  }
  else NEXT_FREEP(fp) = NULL;

  /* new first free block in list */
  PREV_FREEP(fp) = NULL; 
  /* reset start of segregated list */
  seglist[bucket] = fp;
}

/*
 * seg_removeb - remove a free block from the segregated list
 */
static void seg_removeb(void *fp, size_t fsize)
{
  int bucket = seg_search(fsize);

  char *next = NEXT_FREEP(fp);
  char *prev = PREV_FREEP(fp); 

  /* Case: previous block exists */
  if (prev)      /* adjust previous free block's next pointer */
    NEXT_FREEP(prev) = next; 
  /* Case: .. doesn't exist */
  else 
    seglist[bucket] = next; /* adjust start of free list */
  if (next)      /* adjust next free block's previous pointer */
    PREV_FREEP(next) = prev;
}

/*
 * realloc - alias for mm_realloc [UNIMPLEMENTED...]
 */
void *realloc(void *oldptr, size_t size)
{
  size_t oldsize;
  void *newptr;

  /* Special case checks -- */
  if (size == 0) {
    free(oldptr);
    return 0;
  }
  if (oldptr == NULL)
    return malloc(size);

  /* Attempt to malloc -- */
  newptr = malloc(size);
  if (!newptr) return 0;

  /* Copy the old data if malloc successful -- */
  oldsize = GET_SIZE(HDRP(oldptr));
  if (size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

  /* Free the old block. */
  free(oldptr);

  return newptr;
}


/****************************
 * HELPER FUNCTIONS FROM TEXT
 ****************************/

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
  char *bp;
  size_t esize;

  /* Ensure that # of words is aligned & at least MIN_BLK_SIZE */
  esize = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
  if (esize < MIN_BLK_SIZE)
    esize = MIN_BLK_SIZE;

  /* Extend the heap by size */
  if ((long)(bp = mem_sbrk(esize)) == -1)
    return NULL; /* if heap extension fails, return NULL ptr */

  /* Initialize free block header/footer and the epilogue hceader */
  PUT(HDRP(bp), PACK(esize, 0));           /* Free block header */
  PUT(FTRP(bp), PACK(esize, 0));           /* Free block footer */ 
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue header */

  /* Coalesce if this isn't only free block */
  return coalesce(bp);
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));   
  u_int dif = csize - asize;

  /* Remove free block bp no matter what */
  seg_removeb(bp, asize);

  /* If enough space: change header & footer, split, then coalesce */
  if (dif >= MIN_BLK_SIZE) { 
    /* Setup allocated block */
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    /* Enough space for another free block, so setup new free block */
    PUT_WTAG(HDRP(bp), PACK(dif, 0));
    PUT_WTAG(FTRP(bp), PACK(dif, 0));
    /* Insert new free block */
    seg_insertb(bp, dif);
  } 
  /* If remaining space isn't enough, don't split free block */
  else { 
    PUT_WTAG(HDRP(bp), PACK(csize, 1));
    PUT_WTAG(FTRP(bp), PACK(csize, 1)); 
  }
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
  /* Select segregated list */
  int bucket = seg_search(asize);

  /* Search segregated list for fit */
  char *fp;
  while ( ((fp = seg_fit(bucket, asize)) == NULL) && (bucket < (NUM_LISTS-1)) )
        { bucket++; } /* increment bucket every time fit not found */
  
  return fp;
}

/*
 * seg_fit - search free list starting at seglist[bucket] for size;
 *           return ptr to found fit, NULL if no fit found
 */
static void *seg_fit(int bucket, size_t size) 
{
  /* Get start of segregated list */
  char *fp = seglist[bucket];
  printf("list start = %p", fp);
  while (fp) {
    if (size <= GET_SIZE(HDRP(fp)))
      return fp;
    fp = NEXT_FREEP(fp);
  }
  return NULL; /* fit not found */
}


/*******************************************************
 ******* MM_CHECKHEAP - check all aspects of heap & list
 *******************************************************/
void mm_checkheap(int lineno)
{
  /* This routine is always verbose */
  printf("################### %d ################### \n", lineno);
  mylistcheck(); 
  printf("########################################## \n");
  lineno = lineno;
}


/****************************
 * DEBUGGING HELPER FUNCTIONS
 ****************************/

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p)
{
  return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p)
{
  return (size_t)ALIGN(p) == (size_t)p;
}

/* 
 * mylistcheck - Checking essential aspects of free list
 *
 * 1. check essential aspects of heap:
 *    - epilogue & prologue blocks
 *    - address alignment
 *    - blocks are w/in heap boundaries
 *    - header & footer agreement
 *    - coalescing: no two consecutive free blocks in the heap 
 * 2. all next/previous pointers are consistent
 * 3. all free list pointers between mem_heap_lo() & mem_heap_high()
 * 4. free block count thru entire heap == free block count thru free list                                       
 * 5. all blocks in each list bucket fall w/in bucket size range
 */
static void mylistcheck()
{
  char *bp, *fp;
  char *pro = heap_listp + DSIZE;
  int heap_counter = 0;
  int list_counter = 0;

  /* Lowest heap address should be mem_heap_lo() */
  if ((heap_listp) != mem_heap_lo())
    printf("(heap start)"); 

  /* Prologue block's header & footer should agree; 
   * its size should be 8 bytes & it should be allocated */
  if ((GET_SIZE(HDRP(pro)) != DSIZE) || !GET_ALLOC(HDRP(pro)))
    printf("(bad prologue HDR)");
  if ((GET_SIZE(FTRP(pro)) != DSIZE) || !GET_ALLOC(FTRP(pro)))
    printf("(bad prologue FTR)");
  checkb(pro);

  /* Check all blocks in heap */
  printf("-- HEAP TRAVERSAL --\n");
  for (bp = NEXT_BLKP(pro); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (!GET_ALLOC(HDRP(bp))) heap_counter++;
    printb(bp);                     
    checkb(bp);
  } /* bp should now point to the epilogue of the heap */
  printf("\n");

  /* Check all blocks in free list */
  printf("\n-- FREE LIST TRAVERSAL --\n");
  int i = 0;
  for (i = 0; i < NUM_LISTS; i++) {
    fp = seglist[i];
    while (fp != NULL) {
      printfree(fp);
      checkb(fp);
      list_counter++;
      fp = NEXT_FREEP(fp);
    }
  }
  printf("\n");

  /* Epilogue block's header should indicate is has 
   * a size of 0 and is allocated */
  if ((GET_SIZE(HDRP(bp)) != 0) || (!GET_ALLOC(HDRP(bp))))
    printf("(bad epilogue)");

  /* Compare counters for inconsistency */
  if (heap_counter != list_counter)
    printf("Free counts don't match\n");
}

/*
 * printb - Print header & footer of bp
 */
static void printb(void *bp) 
{
  size_t hsize, halloc; /* Header bit encodings */
  size_t fsize, falloc; /* Footer bit encodings */

  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOC(HDRP(bp));
  fsize = GET_SIZE(FTRP(bp));   // FTRP!
  falloc = GET_ALLOC(FTRP(bp)); // FTRP!

  if (hsize == 0) { /* if the block size is 0, end of heap */
    printf("(EOL @ %p)\n", bp);
    return;
  }

  /* Useful debugging info.. */
  printf("%p %c:[[%u:%c][%u:%c]]\n", bp,
          (halloc ? 'A' : 'F'),
          (u_int)hsize, (halloc ? '1' : '0'), 
          (u_int)fsize, (falloc ? '1' : '0'));
}

/*
 * printfree - prints a block in a free list
 */
static void printfree(void *fp)
{
  size_t hsize, halloc; /* Header bit encodings */
  size_t fsize, falloc; /* Footer bit encodings */
  void *next, *prev;    /* NEXT & PREV pointers */

  /* Initialize sizes & allocations */
  hsize = GET_SIZE(HDRP(fp));
  halloc = GET_ALLOC(HDRP(fp));
  fsize = GET_SIZE(FTRP(fp));   
  falloc = GET_ALLOC(FTRP(fp)); 
  /* Initialize next & prev pointers */
  next = NEXT_FREEP(fp);
  prev = PREV_FREEP(fp);

  if (prev == NULL)   /* start of free list */
    printf("[START] ");
  else {              /* print PREV_FREEP(fp) block */
    size_t psize, palloc; /* PREV bit encodings */
    psize = GET_SIZE(HDRP(prev));
    palloc = GET_ALLOC(HDRP(prev));
    printf("[%c:%u|%d]<--", (palloc ? 'a' : 'f'), 
            (u_int)psize, (int)palloc);
  }
 
  if (hsize != 0) {   /* print free block */
    printf("%p %c:[[%u:%c][%u:%c]]", fp,
            (halloc ? 'A' : 'F'),
            (u_int)hsize, (halloc ? '1' : '0'), 
            (u_int)fsize, (falloc ? '1' : '0'));
  }
  else {              /* print epilogue */
    printf("%p %c:[%u:%c]", fp,
            (halloc ? 'A' : 'F'),
            (u_int)hsize, (halloc ? '1' : '0'));
  }

  if (next != NULL && in_heap(next)) { /* print PREV_FREEP(fp) block */
    size_t nsize, nalloc;     /* NEXT bit encodings */
    nsize = GET_SIZE(HDRP(next));
    nalloc = GET_ALLOC(HDRP(next));

    printf("-->[%c:%u|%d] ", (nalloc ? 'a' : 'f'), 
            (u_int)nsize, (int)nalloc);
  }
  else                /* end of free list */
    printf(" [END]");
}

/*
 * checkb - exhaustive check for a given block
 */
static void checkb(void *bp) 
{
  /* ALL BLOCKS must be aligned, in the heap, and have 
   * agreement between their header & footer */
  // Alignment
  if (!aligned(bp)) 
    printf("(!aligned)");
  // In the heap
  if (!in_heap(bp)) 
    printf("(!in_heap)");
  // Header & footer agreement
  if (GET(HDRP(bp)) != GET(FTRP(bp))) 
    printf("(header != footer)");

  /* If this is a FREE BLOCK, it shouldn't have any adjacent
   * free blocks (coalescing), its pointers should agree
   * with their respective destination blocks, and their size 
   * should fall within the range of their size class. */
  if (!GET_ALLOC(HDRP(bp))) {
    /* Init next & prev pointers for bp */
    char *next = NEXT_FREEP(bp);
    char *prev = PREV_FREEP(bp);
    /* Init free block's size & bucket */
    size_t fsize = GET_SIZE(HDRP(bp));
    u_int bucket = seg_search(fsize);
    u_int lower = 1, upper = 1;
    /* Init lower & upper bound for bucket size range */
    u_int i; 
    for (i = 0; i < bucket + 4; i++) {
      if (i == 0) upper *= 2;
      else { lower *= 2; upper *= 2; }
    } /* lower = 2^(bucket + 4), upper = 2^(bucket + 5) */

    // Fall within bucket size range
    if ((fsize < lower) || (fsize >= upper))
      printf("bucket");
    // Coalescing & linkage
    if (next != NULL) { 
      if (prev == NULL) { /* FIRST BLOCK in free list */
        // FIRST BLOCK: coalescing
        if (next == NEXT_BLKP(bp))
          printf("(bad coalescing)");
        // FIRST BLOCK: next pointer linked
        if (bp != PREV_FREEP(next))
          printf("(bad linking)");
      }
      else {              /* MIDDLE BLOCK in free list */
        // MIDDLE BLOCK: coalescing
        if ((next == NEXT_BLKP(bp)) || (prev == PREV_BLKP(bp))) 
          printf("(bad coalescing)");
        // MIDDLE BLOCK: next & prev pointers linked
        if ((bp != NEXT_FREEP(prev)) || (bp != PREV_FREEP(next)))
          printf("(bad linking)");
      }
    }
    else {                /* LAST BLOCK in free list */
      if (prev != NULL) {
        // LAST BLOCK: coalescing
        if (prev == PREV_BLKP(bp)) 
          printf("(bad coalescing)");
        // LAST BLOCK: prev pointer linked
        if (bp != NEXT_FREEP(prev))
          printf("(bad linking)");
      } /* otherwise, ONLY BLOCK in free list */
    }
  }
}














