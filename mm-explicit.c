/*
 * mm.c
 *
 * Jack Kasbeer (jkasbeer)
 * July 14, 2015
 *
 * Slightly more complicated, 32-bit and 64-bit clean allocator based on 
 * EXPLICIT free lists, LIFO free block ordering, FIRST FIT placement, and 
 * boundary tag coalescing, as described in the CS:APP2e text. 
 * Blocks must be aligned to doubleword (8 byte) boundaries. 
 * Minimum block size is 24 bytes. 
 *
 * Passed all traces.
 * $Perfindex = 40(util) + 39(thru)
 *            = 79
 */

/********************************************* BLOCK INFO ****************************************************

 * HEADER:       4 bytes
 * NEXT POINTER: 8 bytes
 * PREV POINTER: 8 bytes
 * FOOTER:       4 bytes
 
 < Allocated Block >
 
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |  | A|
    bp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                                                                                               |
            |                                                                                               |
            .                              Payload and padding                                              .
            .                                                                                               .
            .                                                                                               .
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |  |  | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 
 
 < Free block >
 
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |  | A|
    fp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                            pointer to next free block in free list                            |
            |                                                                                               |
fp+DSIZE--> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                        pointer to previous free block in free list                            |
            |                                                                                               |
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |  |  | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+

***************************************** END OF BLOCK INFO **************************************************/

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

/* Single word (4) aligned or double word (8) aligned */
#define ALIGNMENT     8       /* DSIZE alignment for 64-bit machines */

/* ## GENERAL MACROS ## */

/* Basic constants and macros */
#define WSIZE         4       /* Word and header/footer size (bytes) */
#define DSIZE         8       /* Doubleword size (bytes) */
#define OVERHEAD      8       /* Needed for prologue alignment */
#define MIN_BLK_SIZE 24       /* Next & prev ptr's 8 bytes for 64-bit */
#define INITSIZE     (1<<6)   /* Chunksize specific to mm_init */
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
#define HDRP(bp)       ( (void *)(bp) - WSIZE )
#define FTRP(bp)       ( (void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE ) 

/* Given block ptr bp, compute address of next & previous blocks */
#define NEXT_BLKP(bp)  ( (void *)(bp) + GET_SIZE(((void *)(bp) - WSIZE)) )
#define PREV_BLKP(bp)  ( (void *)(bp) - GET_SIZE(((void *)(bp) - DSIZE)) )

/* ## EXPLICIT FREE LIST MACROS ## */

/* Compute address of next & prev free block entries */
#define NEXT_FREEP(bp) ( *(void **)bp )
#define PREV_FREEP(bp) ( *(void **)(bp + DSIZE) )

/* Global variables */
static char *heap_listp = 0;    /* Pointer to first block */
static char *free_listp = 0;    /* Pointer to first free block */

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);     
static void place(void *ptr, size_t asize); 
static void *find_fit(size_t asize);        
static void *coalesce(void *ptr);           
static void removeb(void *fp);
static void insertb(void *fp);
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
  /* Check for error then initialize empty heap */
  if (!(heap_listp = mem_sbrk(4*WSIZE)))  return -1;

  /* Set up the heap with padding, prologue, and epilogue */
  PUT(heap_listp, 0);                          /* Alignment padding */
  PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
  PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
  PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */

  free_listp = NULL;

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
    extendsize = (MAX(asize, CHUNKSIZE)) / WSIZE;
    if (!(bp = extend_heap(extendsize)))  return NULL;
  }

  /* Allocate space in memory before returning */
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

  //REMOVE_TAG(HDRP(NEXT_BLKP(bp)));
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
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc)              /* Case 1 */
    bp = bp; 
  else if (prev_alloc && !next_alloc) {      /* Case 2 */
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    removeb(NEXT_BLKP(bp)); 
    PUT_WTAG(HDRP(bp), PACK(size, 0));   
    PUT_WTAG(FTRP(bp), PACK(size, 0));                  
  }
  else if (!prev_alloc && next_alloc) {      /* Case 3 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    bp = PREV_BLKP(bp);                 /* adjust bp for insertion */
    PUT_WTAG(HDRP(bp), PACK(size, 0));
    PUT_WTAG(FTRP(bp), PACK(size, 0)); 
    removeb(bp);             
  }
  else {                                     /* Case 4 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));  
    removeb(NEXT_BLKP(bp));  
    PUT_WTAG(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT_WTAG(FTRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);                 /* adjust bp for insertion */
    removeb(bp);            
  }

  /* Insert new free block in list */
  insertb(bp);

  return bp;
}

/*
 * removeb - removes a block from the free list & reorganizes 
 *           free block pointers if necessary.
 */
static void removeb(void *fp)
{
  void *prev = PREV_FREEP(fp); 
  void *next = NEXT_FREEP(fp);

  /* If there's a previous free block... */
  if (prev)  NEXT_FREEP(PREV_FREEP(fp)) = NEXT_FREEP(fp); 
  /* If not, next free block is the new start */
  else  free_listp = NEXT_FREEP(fp); 
  /* If there's a next free block... */
  if (next)  PREV_FREEP(NEXT_FREEP(fp)) = PREV_FREEP(fp);
}

/*
 * insertb - uses a LIFO placement policy to insert a free
 *           block at the start of the free list
 */
static void insertb(void *fp)
{
  if (free_listp) {
    /* previous free list start now needs prev ptr */
    PREV_FREEP(free_listp) = fp; 
    /* set next free ptr to old start of list */
    NEXT_FREEP(fp) = free_listp; 
  }
  else  NEXT_FREEP(fp) = NULL;

  /* new first free block in list */
  PREV_FREEP(fp) = NULL; 
  /* reset start of free list */
  free_listp = fp;       
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
  if ((long)(bp = mem_sbrk(esize)) == -1)  return NULL; 

  /* Initialize free block header/footer and the epilogue hceader */
  PUT(HDRP(bp), PACK(esize, 0));           /* Free block header */
  PUT(FTRP(bp), PACK(esize, 0));           /* Free block footer */ 
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue header */
  /* Coalesce if there are more free blocks in list */
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
  removeb(bp);

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
    insertb(bp);
  } 
  else { /* If remaining space isn't enough, don't split free block */
    PUT_WTAG(HDRP(bp), PACK(csize, 1));
    PUT_WTAG(FTRP(bp), PACK(csize, 1)); 
  }
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
  void *fp = free_listp;
  /* Search free list for big enough block */
  while (fp) { 
    if (asize <= GET_SIZE(HDRP(fp)))  return fp;
    fp = NEXT_FREEP(fp);
  }

  return NULL; /* no fit */
}


/*********************
 * DEBUGGING FUNCTIONS
 *********************/

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


/*****************************
 *mm_checkheap helper routines
 *****************************/

/* IMPLICIT, EXPLICIT, AND SEGREGATED FREE LIST 
 * myheapcheck - Check all essential aspects of heap
 *             1. check epilogue & prologue blocks
 *             2. check each block's address alignment
 *             3. check heap boundaries
 *             4. check each block's header & footer (agreement)
 *             5. check coalescing: no two consecutive free blocks in the heap 
 *                (FINISH!)
 */

/* EXPLICIT & SEGREGATED FREE LIST
 * mylistcheck - Checking essential aspects of free list
 *             1. check essential aspects of heap
 *             2. all next/previous pointers are consistent
 *             3. all free list pointers between mem_heap_lo() & mem_heap_high()
 *             4. free block count thru entire heap == free block count thru 
 *                free list                                       
 *             5. SEGREGATED ONLY: all blocks in each list bucket fall w/in
 *                bucket size range
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
  fp = free_listp;
  while (fp != NULL) { 
    printfree(fp);
    checkb(fp);
    list_counter++;
    fp = NEXT_FREEP(fp);
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


/************************************
 * Private list check helper routines 
 ************************************/
/*
 * printb - Print header & footer of bp
 *          Useful helper function for debugging.
 */
static void printb(void *bp) 
{
  size_t hsize, halloc; /* Header bit encodings */
  size_t fsize, falloc; /* Footer bit encodings */

  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOC(HDRP(bp));
  fsize = GET_SIZE(FTRP(bp));   
  falloc = GET_ALLOC(FTRP(bp));

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
  // alignment
  if (!aligned(bp)) 
    printf("(!aligned)");
  // in the heap
  if (!in_heap(bp)) 
    printf("(!in_heap)");
  // header & footer agreement
  if (GET(HDRP(bp)) != GET(FTRP(bp))) 
    printf("(header != footer)");

  /* If this is a FREE BLOCK, it shouldn't have any adjacent
   * free blocks (coalescing) and its pointers should agree
   * with their respective destination blocks */
  if (!GET_ALLOC(HDRP(bp))) {
    char *next = NEXT_FREEP(bp);
    char *prev = PREV_FREEP(bp);
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
      } 
      /* otherwise, ONLY BLOCK in free list */
    }
  }
}














