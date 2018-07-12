/*
 * mm.c
 *
 * Jack Kasbeer (jkasbeer)
 * July 14, 2015
 *
 * Simple, 32-bit and 64-bit clean allocator based on IMPLICIT free
 * lists, NEXT FIT placement, and boundary tag coalescing, as described
 * in the CS:APP2e text. Also note that colescing occurs once we've run 
 * out of space.Blocks must be aligned to doubleword (8 byte) boundaries.
 * Minimum block size is 16 bytes. 
 *
 * Passes all traces.
 * $Perfindex = 38(util) + 11(thru)
 *            = 49
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

/*
 * If NEXT_FIT defined use next fit search, else use first fit search 
 */
#define NEXT_FIT

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define ALIGNMENT   8
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */

/* Determine larger variable, given two */
#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */ 
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
/*  NOTE!
 * Header:    [    MSB's(29)   |  LSB's(3) ]
 * Footer:    [    MSB's(29)   |  LSB's(3) ] (identical)
 * least significant byte of header: allocate?.. most significant bytes: size
 */

/* ## IMPLICIT FREE LIST MACROS ## */
/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 
/*  NOTE! 
 * Block:     [ HDR |    PAYLOAD    | FTR ]
 * HDRP: header is word away from block content
 * FTRP: add size (includes hdr & ftr), then subtract hdr+ftr size
 */

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static char *og_heap_listp = 0;
#ifdef NEXT_FIT
static char *traveler;        /* Next fit traveler pointer */
#endif

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);     /* Additional heap ext. function */
static void place(void *ptr, size_t asize); /* Text book exercise: place block */
static void *find_fit(size_t asize);        /* Test book exercise: search for place to PUT */ 
static void *coalesce(void *ptr);           /* Merge free blocks */
/* Function prototypes for debugging routines */
static void myheapcheck(); 
static void mylistcheck();       
static void printb(void *blok);             
static void checkb(void *blok);      
static int in_heap(const void *p);
static int aligned(const void *p);       

/* NOTE: change header and footer size to much smaller */
/* NOTE: mem_sbrk(0) will return the current location of the program brk */

/*
 * mm_init - initialize an empty heap: return -1 on error, 0 on success.
 */
int mm_init(void) 
{
  /* Check for error then initialize empty heap */
  if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) 
    return -1;

  /* Set up the heap with padding, prologue, and epilogue */
  PUT(heap_listp, 0);                          /* Alignment padding */
  PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
  PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
  PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
  /* Minor optimization: move heap_listp to first block after HDR */
  heap_listp += (4*WSIZE);
  og_heap_listp = heap_listp - (2*WSIZE); /* keep track of prologue */

/****** NEXT FIT IMPL. ******/
#ifdef NEXT_FIT
  /* Next fit ==> initialize traveler */
  traveler = heap_listp;
#endif
/****************************/

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
    return -1; //failure

  assert(in_heap(heap_listp));
  assert(aligned(heap_listp));

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
  if (heap_listp == 0) mm_init();
  if (size == 0) return NULL;

  /* Typical malloc cases -- */
  if (size <= DSIZE) /* less than a double, easy */
    asize = 2*DSIZE; /* 8 bytes: hdr & ftr, alloc space: <= 8 bytes */
  else               /* calc how many dwords needed */
    asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

  /* Search for a fit.. return immediately if found */
  if ((bp = find_fit(asize)) != NULL) { 
    place(bp, asize); 
    return bp;
  } /* No fit found ==> need more heap! */
  extendsize = MAX(asize,CHUNKSIZE); 
  if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
    return NULL; 

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
  if (bp == 0) return;
  if (heap_listp == 0) mm_init();

  size_t size = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));  // FTRP!
  coalesce(bp);
}

/*
 * coalesce - Boundary tag coalescing; return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  // FTRP!
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc)              /* Case 1 */
    return bp;
  else if (prev_alloc && !next_alloc) {      /* Case 2 */
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size,0));                       // FTRP!
  }
  else if (!prev_alloc && next_alloc) {      /* Case 3 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));                      // FTRP!
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  else {                                     /* Case 4 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));             // FTRP!
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));           // FTRP!
    bp = PREV_BLKP(bp);
  }

/****** NEXT FIT IMPL. ******/
#ifdef NEXT_FIT
  /* Make sure the traveler isn't pointing into the free block
   * that we just coalesced */
  if ((traveler > (char *)bp) && (traveler < NEXT_BLKP(bp))) 
    traveler = bp;
#endif
/****************************/

  return bp;
}

/*
 * realloc - alias for mm_realloc
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
  size_t size;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
  if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL; /* if heap extension fails, return NULL ptr */

  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0));         /* Free block header */ 
  PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */     // FTRP!
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

  /* Coalesce if the previous block was free */
  return coalesce(bp);  
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));   

  u_int pack_it, pack_em;
  if ((csize - asize) >= (2*DSIZE)) { pack_it = PACK(asize, 1);
                                      pack_em = PACK(csize-asize, 0);
    PUT(HDRP(bp), pack_it);
    PUT(FTRP(bp), pack_it);     // FTRP!
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), pack_em);
    PUT(FTRP(bp), pack_em);     // FTRP!
  }
  else { pack_it = PACK(csize, 1);
    PUT(HDRP(bp), pack_it);
    PUT(FTRP(bp), pack_it);     // FTRP!
  }
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
  /* Next fit search */
  #ifdef NEXT_FIT 

  char *oldtraveler = traveler;

  /* Search from the traveler to the end of list */
  for ( ; GET_SIZE(HDRP(traveler)) > 0; traveler = NEXT_BLKP(traveler)) {
    if (!GET_ALLOC(HDRP(traveler)) && (asize <= GET_SIZE(HDRP(traveler))))
      return traveler;
  }

  /* Search from start of list to old traveler */
  for (traveler = heap_listp; traveler < oldtraveler; traveler = NEXT_BLKP(traveler)) {
    if (!GET_ALLOC(HDRP(traveler)) && (asize <= GET_SIZE(HDRP(traveler))))
      return traveler;
  }
  return NULL;  /* no fit found */

  /* First fit search */
  #else

  void *bp;

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
      return bp;
  }
  return NULL; /* No fit */

  #endif
}

/*********************
 * DEBUGGING FUNCTIONS
 *********************/

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
  return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
  return (size_t)ALIGN(p) == (size_t)p;
}

/************************************************************************
 ******* MM_CHECKHEAP - check all aspects of heap & [NOT FINISHED]
 ************************************************************************/
void mm_checkheap(int lineno) {
  /* This routine is always verbose */
  //printf("LINE: %d\n", lineno);
  printf("################### HEAP ################### \n");
  myheapcheck();
  mylistcheck(); // currently does nothing
  printf("############################################ \n\n");
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
 *             5. check coalescing: no two consecutive free blocks in the heap (FINISH!)
 */
static void myheapcheck() 
{
  char *bp = og_heap_listp;
  /* Check prologue block */
  if ((GET_SIZE(HDRP(og_heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(og_heap_listp))) {
    printf("Bad prologue header\n");
  }
  checkb(og_heap_listp);

  /* Check all blocks in heap */
  for (bp = og_heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    printb(bp);
    if (bp == og_heap_listp) { /* check heap start boundary */
      if ((bp-DSIZE) != mem_heap_lo())
        printf("Bad heap start\n"); 
    }                          /* check for consecutive free blocks */
    if ((GET_ALLOC(HDRP(bp)) == 0) && (GET_ALLOC(HDRP(NEXT_BLKP(bp)))) == 0)
      printf("Bad coalescing\n");
    checkb(bp);
  }
  /* Check epilogue block */
  printb(bp);
  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
    printf("Bad epilogue header\n");
  if ((bp-1) != mem_heap_hi())   /* check heap end boundary */
    printf("Bad heap end\n");
}

/* EXPLICIT & SEGREGATED FREE LIST
 * mylistcheck - Checking essential aspects of free list
 *             1. all next/previous pointers are consistent
 *             2. all free list pointers between mem_heap_lo() & mem_heap_high()
 *             3. free block count thru entire heap == free block count thru 
 *                free list                                       
 *             4. SEGREGATED ONLY: all blocks in each list bucket fall w/in
 *                bucket size range
 */
static void mylistcheck()
{
  /* UNIMPLIMENTED     */
}


/************************************
 * Private heap check helper routines 
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
  fsize = GET_SIZE(FTRP(bp));   // FTRP!
  falloc = GET_ALLOC(FTRP(bp)); // FTRP!

  if (hsize == 0) { /* if the block size is 0, end of heap */
    printf("%c: header: [%u:%c]  ",(halloc ? 'A' : 'F'),
          (u_int)hsize, (halloc ? 'a' : 'f'));
    printf("(EOL @ %p)\n", bp);
    return;
  }

  /* Useful debugging info.. */
  printf("%c: header: [%u:%c] footer: [%u:%c]\n",
          (halloc ? 'A' : 'F'),
          (u_int)hsize, (halloc ? 'a' : 'f'), 
          (u_int)fsize, (falloc ? 'a' : 'f'));
}

/*
 * checkb - alignment & header=footer check on bp
 *          Helper function for checkheap.
 */
static void checkb(void *bp) 
{
  if (!aligned(bp)) /* Check block alignment */
    printf("Error: %p is not doubleword aligned\n", bp);
  if (GET(HDRP(bp)) != GET(FTRP(bp))) /* Check header & footer agreement */  // FTRP!
    printf("Error: header does not match footer\n");
}






