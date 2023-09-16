/*
    할당: 2^k를 할당해야 할 때, k <= j인 j를 찾는다. 이후 크기가 2^j인 free block을 반씩 나누고, 한쪽은 seg list에 노드로 연결하고 한쪽은 크기가 2^k가 아니라면 재귀적으로 나누면서 최소 seg list의 클래스 크기가 될 때까지 줄인다. 2^k와 같아지는 순간 해당 블록에 할당.
    해제: 해제 역시 재귀적으로 수행된다. 할당된 블록은 ||| | |  |  |    |     |    이런식으로 나뉘어져 있고, 자기와 크기가 같은 free block을 buddy라고 한다. free시킬 블록의 오른쪽편 블록이 비할당이면 자신의 버디이므로 합쳐주고, 이렇게 합쳐주다가 할당된 블록을 만나면 자기의 버디가 아니므로 합치기를 중단하고 합친거를 seg list에 넣어준다. 합쳐가면서 합쳐진 블록은 seg list에서 삭제시켜줘야 한다. 삽입 삭제: explicit 함수 응용. 
*/

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
  /* Team name */
  "test",
  /* First member's full name */
  "test",
  /* First member's NYU NetID*/
  "test",
  /* Second member's full name (leave blank if none) */
  "",
  /* Second member's email address (leave blank if none) */
  ""
};


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


// My additional Macros
#define WSIZE     4          // word and header/footer size (bytes)
#define DSIZE     8          // double word size (bytes)
#define INITCHUNKSIZE (1<<20)
#define CHUNKSIZE (1<<12)//+(1<<7) 

#define LISTLIMIT     21     
#define REALLOC_BUFFER  (1<<7)    

#define MAX(x, y) ((x) > (y) ? (x) : (y)) 
#define MIN(x, y) ((x) < (y) ? (x) : (y)) 

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word at address p 
#define GET(p)            (*(unsigned int *)(p))
#define PUT(p, val)       (*(unsigned int *)(p) = (val))
#define PUT_NOTAG(p, val) (*(unsigned int *)(p) = (val))

// Store predecessor or successor pointer for free blocks 
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

// Read the size and allocation bit from address p 
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_TAG(p)   (GET(p) & 0x2)
#define SET_RATAG(p)   (GET(p) |= 0x2)
#define REMOVE_RATAG(p) (GET(p) &= ~0x2)

// Address of block's header and footer 
#define HDRP(ptr) ((char *)(ptr) - WSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

// Address of (physically) next and previous blocks 
#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))
#define PREV_BLKP(ptr) ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))

// Address of free block's predecessor and successor entries 
#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)

// Address of free block's predecessor and successor on the segregated list 
#define PRED(ptr) (*(char **)(ptr))
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))


/* 매크로 wrapper 함수 */
static size_t _get(p) {return GET(p);}
static void _put(p, val) {PUT(p, val);}
static int _get_size(p) {return GET_SIZE(p);}
static int _get_alloc(p) {return GET_ALLOC(p);}
static char* _hdrp(bp) {return HDRP(bp);}
static char* _ftrp(bp) {return FTRP(bp);}
static char* _next_blkp(bp) {return NEXT_BLKP(bp);}
static char* _prev_blkp(bp) {return PREV_BLKP(bp);}

// Global var
void *segregated_free_lists[LISTLIMIT]; 
char *free_start;

// Functions
static void *extend_heap(size_t size);
static void *coalesce(void *ptr);
static void *place(void *ptr, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);
static int get_exp(int size);
//static void checkheap(int verbose);


///////////////////////////////// Block information /////////////////////////////////////////////////////////
/*
 
A   : Allocated? (1: true, 0:false)
RA  : Reallocation tag (1: true, 0:false)
 
 < Allocated Block >
 
 
             31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |  | A|
    bp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                                                                                               |
            |                                                                                               |
            .                              Payload and padding                                              .
            .                                                                                               .
            .                                                                                               .
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 
 
 < Free block >
 
             31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |RA| A|
    bp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                        pointer to its predecessor in Segregated list                          |
bp+WSIZE--> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                        pointer to its successor in Segregated list                            |
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            .                                                                                               .
            .                                                                                               .
            .                                                                                               .
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 
 
*/
///////////////////////////////// End of Block information /////////////////////////////////////////////////////////

//////////////////////////////////////// Helper functions //////////////////////////////////////////////////////////
static void *extend_heap(size_t size)
{
    void *ptr;                   
    size_t asize;                // Adjusted size 
    
    size_t exp = 1;

    while (size > (1<<exp)) {
        exp += 1;
    }

    asize = 1<<exp;
    
    if ((ptr = mem_sbrk(asize)) == (void *)-1)
        return NULL;
    
    // Set headers and footer 
    PUT_NOTAG(HDRP(ptr), PACK(asize, 0));  
    PUT_NOTAG(FTRP(ptr), PACK(asize, 0));   
    PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); 
    insert_node(ptr, exp);

    return ptr;
}

// 
static void insert_node(void *ptr, size_t exp) {
    void *search_ptr = ptr;

    search_ptr = segregated_free_lists[exp];

    // 들어있는게 있는 경우 
    if (search_ptr != NULL) {
        // 작은게 없으면 맨 앞에 넣기
        SET_PTR(PRED_PTR(ptr), search_ptr);
        SET_PTR(SUCC_PTR(search_ptr), ptr);
        SET_PTR(SUCC_PTR(ptr), NULL);
        segregated_free_lists[exp] = ptr;
    }
    // 들어 있는게 없으면 
    else {
        SET_PTR(PRED_PTR(ptr), NULL);
        SET_PTR(SUCC_PTR(ptr), NULL);
        segregated_free_lists[exp] = ptr;
    }
    return;
}


static void delete_node(void *ptr) {
    size_t size = GET_SIZE(HDRP(ptr));

    int exp = get_exp(size);

    // pred가 아래, succ이 위

    // 아래 노드가 있는 경우,
    if (PRED(ptr) != NULL) {

        // 위 노드도 있는 경우
        if (SUCC(ptr) != NULL) {
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));

        }
        // 위 노드는 없는 경우
        else {
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
            segregated_free_lists[exp] = PRED(ptr);
        }
    }
    
    // 아래 노드가 없는 경우,
    else {
        // 위 노드는 있는 경우
        if (SUCC(ptr) != NULL) {
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL);
        }
        
        // 위 노드도 없는 경우,
        else {
            segregated_free_lists[exp] = NULL;
        }
    }
    
    return;
}


static void *coalesce(void *ptr)
{
    // 병합할 때, 
    while (1) {
        // 버디 찾기
        int buddy_number = (unsigned int*)(HDRP(ptr)) - (unsigned int*)free_start;
        int cur_size = GET_SIZE(HDRP(ptr));

        // 버디넘버가 짝수면 오른쪽에 버디가 있다.
        if (buddy_number % 2 == 0) {
            // 오른쪽이 크기가 같고 할당비트 비할당이면
            if (GET_SIZE(HDRP(NEXT_BLKP(ptr))) == cur_size && GET_ALLOC(HDRP(NEXT_BLKP(ptr))) == 0) {
                // 우선 delete_node 해주기
                delete_node(NEXT_BLKP(ptr));

                // free블록 합쳐주기
                PUT(HDRP(ptr), GET_SIZE(HDRP(ptr)) * 2);
                PUT(FTRP(ptr), GET_SIZE(HDRP(ptr)) * 2);
            }
            else {
                break;
            }
        }

        // 버디넘버가 홀수면 왼쪽에 버디가 있다.
        else {
            if (GET_SIZE(HDRP(PREV_BLKP(ptr))) == cur_size && GET_ALLOC(HDRP(PREV_BLKP(ptr))) == 0) {
                delete_node(PREV_BLKP(ptr));

                PUT(HDRP(PREV_BLKP(ptr)), GET_SIZE(HDRP(ptr)) * 2);
                PUT(FTRP(PREV_BLKP(ptr)), GET_SIZE(HDRP(ptr)) * 2);
                ptr = PREV_BLKP(ptr);
            }
            else {
                break;
            }
        }
    }

    int exp = get_exp(GET_SIZE(HDRP(ptr)));
    // 병합 다 끝냈으면 이제 넣기
    insert_node(ptr, exp);
    
    return ptr;
}

// 안 넣어준거 할당해주기
static void *place(void *ptr, size_t asize)
{
    delete_node(ptr);
    PUT(HDRP(ptr), PACK(asize, 1));
    PUT(FTRP(ptr), PACK(asize, 1));    
    
    return ptr;
}

static void split(void *ptr, size_t asize) {
    // ptr free 블록을 asize가 될 때까지 나눠주기
    // 현재 블록의 크기가 같을 때,
    size_t cur_size = GET_SIZE(HDRP(ptr));

    // 크기가 다를 때 앞 부분을 split 해주고, 뒷 부분은 세그에 넣기
    
    // 헤더 푸터 변환
    PUT_NOTAG(HDRP(ptr), PACK(cur_size / 2, 0));
    PUT_NOTAG(FTRP(ptr), PACK(cur_size / 2, 0));

    // 세그에 넣을 free block
    PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(cur_size / 2, 0));
    PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(cur_size / 2, 0));


    int exp = get_exp(cur_size / 2);

    // 세그에 넣어주기, 
    insert_node(NEXT_BLKP(ptr), exp);
    // 현재 블록 크기/2가 할당할 크기와 같으면 ptr도 넣어주고 ptr;
    if (cur_size/2 == asize) {
        insert_node(ptr, exp);
        return;
    }

    // 그 외엔 또 나눠줘야 하고 반환받은걸 위로 올려주기
    split(ptr, asize);
}

//////////////////////////////////////// End of Helper functions ////////////////////////////////////////



static int get_exp(int size) {
    int exp = 1;

    while (size > (1<<exp)) {
            exp += 1;
        }
    return exp;
}


/*
 * mm_init - initialize the malloc package.
 * Before calling mm_malloc, mm_realloc, or mm_free, 
 * the application program calls mm_init to perform any necessary initializations,
 * such as allocating the initial heap area.
 *
 * Return value : -1 if there was a problem, 0 otherwise.
 */
int mm_init(void)
{
    int list;         
    char *heap_start; // Pointer to beginning of heap
    
    // Initialize segregated free lists
    for (list = 4; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }
    
    // Allocate memory for the initial empty heap 
    if ((long)(heap_start = mem_sbrk(4 * WSIZE)) == -1)
        return -1;
    
    PUT_NOTAG(heap_start, 0);                            /* Alignment padding */
    PUT_NOTAG(heap_start + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT_NOTAG(heap_start + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT_NOTAG(heap_start + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    
    free_start = heap_start + 3*WSIZE;

    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;
    
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 *
 * Role : 
 * 1. The mm_malloc routine returns a pointer to an allocated block payload.
 * 2. The entire allocated block should lie within the heap region.
 * 3. The entire allocated block should overlap with any other chunk.
 * 
 * Return value : Always return the payload pointers that are alligned to 8 bytes.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *ptr = NULL;  /* Pointer */
    int exp = 1;
    // Ignore size 0 cases
    if (size == 0)
        return NULL;
    
    exp = get_exp(size + DSIZE);
    // 2의 제곱꼴로 aglin, 최소 16
    // if (size <= 2 * DSIZE) {
    //     asize = 2 * DSIZE;
    //     exp = 4;
    // } else {
    //     exp = get_exp(size);

    //     asize = 1<<exp;
    // }
    asize = 1<<exp;

    size_t searchsize = asize;
    int list = exp;
    // Search for free block in segregated list
    while (list < LISTLIMIT) {
        // 해당 클래스에 free block 있을 때,
        if ((list == LISTLIMIT - 1) || segregated_free_lists[list] != NULL) {
            // ptr에 해당 free block 넣기
            ptr = segregated_free_lists[list];
            break;
        }
        list++;
    }

    
    // free block 못 찾았으면 힙 확장 후 넣기
    if (ptr == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);
        
        if ((ptr = extend_heap(extendsize)) == NULL)
            return NULL;
    }

    // 해당 free block을 나누어서 seg list에 넣어주기 반환값으로 할당할 free block의 bp 반환
    if (asize < GET_SIZE(HDRP(ptr))) {
        // 나눠줄 블록은 세그에서 삭제하고,
        delete_node(ptr);

        // 나눠준다.
        split(ptr, asize);
    }
    
    // free 블록 받기
    ptr = segregated_free_lists[exp];
    ptr = place(ptr, asize);
    
    // Return pointer to newly allocated block 
    return ptr;
}

/*
 * mm_free - Freeing a block does nothing.
 *
 * Role : The mm_free routine frees the block pointed to by ptr
 *
 * Return value : returns nothing
 */

// free 시켜주기. 
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    int exp = get_exp(size);
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    
    // 버디 찾기
    // 프리시켜줄 블록 왼쪽에 자신과 같은 크기의 블록 개수 세기
    // 우선, 병합을 한다.
    
    coalesce(ptr);
    // insert_node(ptr, exp);
    
    return;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 *
 * Role : The mm_realloc routine returns a pointer to an allocated 
 *        region of at least size bytes with constraints.
 *
 *  I used https://github.com/htian/malloc-lab/blob/master/mm.c source idea to maximize utilization
 *  by using reallocation tags
 *  in reallocation cases (realloc-bal.rep, realloc2-bal.rep)
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr = ptr;    /* Pointer to be returned */
    size_t new_size = size; /* Size of new block */
    int remainder;          /* Adequacy of block sizes */
    int extendsize;         /* Size of heap extension */
    int block_buffer;       /* Size of block buffer */
    
    // Ignore size 0 cases
    if (size == 0)
        return NULL;
    
    // Align block size
    if (new_size <= DSIZE) {
        new_size = 2 * DSIZE;
    } else {
        new_size = ALIGN(size+DSIZE);
    }
    
    /* Add overhead requirements to block size */
    new_size += REALLOC_BUFFER;
    
    /* Calculate block buffer */
    block_buffer = GET_SIZE(HDRP(ptr)) - new_size;
    
    /* Allocate more space if overhead falls below the minimum */
    if (block_buffer < 0) {
        /* Check if next block is a free block or the epilogue block */
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
            remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;
            if (remainder < 0) {
                extendsize = MAX(-remainder, CHUNKSIZE);
                if (extend_heap(extendsize) == NULL)
                    return NULL;
                remainder += extendsize;
            }
            
            delete_node(NEXT_BLKP(ptr));
            
            // Do not split block
            PUT_NOTAG(HDRP(ptr), PACK(new_size + remainder, 1)); 
            PUT_NOTAG(FTRP(ptr), PACK(new_size + remainder, 1)); 
        } else {
            new_ptr = mm_malloc(new_size - DSIZE);
            memcpy(new_ptr, ptr, MIN(size, new_size));
            mm_free(ptr);
        }
        block_buffer = GET_SIZE(HDRP(new_ptr)) - new_size;
    }
    
    // Tag the next block if block overhead drops below twice the overhead 
    if (block_buffer < 2 * REALLOC_BUFFER)
        SET_RATAG(HDRP(NEXT_BLKP(new_ptr)));
    
    // Return the reallocated block 
    return new_ptr;
}

