# Introduction to Computer Systems (15-213/16-213)
# Malloc Lab
##### Carnegie Mellon University; Nathaniel Filardo

### Author: Jack Kasbeer
### Created: July, 2015

## Overview
Dynamic memory allocator: 32-bit and 64-bit clean allocator based on SEGREGATED fit
lists, LIFO free block ordering, FIRST FIT placement, and boundary tag coalescing, 
as described in the CS:APP2e text. 
Blocks must be aligned to doubleword (8 byte) 
boundaries. 
Minimum block size is 24 bytes. 
##### Example Block
```C
/*
Block:  F [ HDR | NEXTP | PREVP | FTR ] 
        A [ HDR |    PAYLOADS   | FTR ]
Bytes:      4      8        8      4   ==> MIN_BLK_SIZE = 24 bytes
*/
```

## mm.c
### The really cool MACROS and performance giveaways
```C
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
```

### Implemented Functions
```C
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
``` 

### My Memory Dynamnic Allocator (mmalloc)
```C
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
```




















