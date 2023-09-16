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
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* implicit free list 세팅값 및 매크로 함수들*/
#define WSIZE   4 // 워드 사이즈(bytes), 헤더, 푸터 크기
#define DSIZE   8 // 더블 워드 사이즈(bytes)
#define CHUNKSIZE (1<<12) // 힙 사이즈, 4096BYTEs

#define MAX(x, y) ((x) > (y)? (x) : (y)) 

// /*사이즈와 할당비트를 하나의 워드로 만든다*/
#define PACK(size, alloc) ((size) | (alloc))

// /* 주소 p를 읽어오기 */
#define GET(p) (*(unsigned int *)(p))

// /* 주소 p에 쓰기*/
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 크기와 할당여부 읽기 */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 헤더 주소 계산 */
// bp = payload 시작주소
#define HDRP(bp) ((char *)((bp) - WSIZE))
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // base point + 블록 크기 - DSIZE(푸터(헤더) 크기*2)

/*다음 블록과 이전 블록주소를 알아내는 매크로*/
// 현재 블록 padding 주소 + 현재 블록 크기 = 다음 블록 bp
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define LISTLIMIT 21
// 현재 블록 padding 주소 - 이전 블록 크기 = 이전 블록 bp
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
#define MIN_BLOCK_SIZE 8
#define SUCC_P(bp)  (*(void **)((bp)+WSIZE))
static void list_add(void *p);
static void list_remove(void *p, int class);
static char* heap_listp; // 힙의 첫 바이트주소
/* 매크로 wrapper 함수 */
static size_t _get(p) {return GET(p);}
static void _put(p, val) {PUT(p, val);}
static int _get_size(p) {return GET_SIZE(p);}
static int _get_alloc(p) {return GET_ALLOC(p);}
static char* _hdrp(bp) {return HDRP(bp);}
static char* _ftrp(bp) {return FTRP(bp);}
static char* _next_blkp(bp) {return NEXT_BLKP(bp);}
static char* _prev_blkp(bp) {return PREV_BLKP(bp);}
// static size_t get_class(size_t adjusted_size) {
//     size_t res = 8;
//     size_t cls = 0;
//     while (adjusted_size > res) {
//         res <<= 1;
//         cls++;
//     }
//     return cls; 
// }

static int get_exp(int size) {
    int exp = 1;

    while (size > (1<<exp)) {
            exp += 1;
        }
    return exp;
}

static void *segregated_free_lists[LISTLIMIT]; 
static char* segregated_free_lists[20];
static size_t class_size[20];

// 맨앞에 추가
static void list_add(void *p){
    int block_size = (int)((unsigned int*)GET(HDRP(p)) - (unsigned int*)(HDRP(p)));
    
    int exp = get_exp(block_size);

    // 아무것도 없으면 그냥 연결
    if (segregated_free_lists[exp] == NULL) {
        segregated_free_lists[exp] = HDRP(p);
    }

    // 있으면 사이에 연결
    else {
        PUT(HDRP(p), segregated_free_lists[exp]);
        segregated_free_lists[exp] = HDRP(p);
    }
}

// 맨앞노드 삭제
static void list_remove(int exp){
    // 이거밖에 없을 때
    if (GET(segregated_free_lists[exp]) == NULL) {
        segregated_free_lists[exp] = NULL
    }
    // 다른거 있을 때
    else {
        segregated_free_lists[exp] = GET(segregated_free_lists[exp]);       
    }
}

static void* extend_heap(size_t words) {
    char* bp;
    size_t size;
    int exp;
    int adjusted_size;

    exp = get_exp(words * 4);
    adjusted_size = (1 << exp);

    if ((long)(bp = mem_sbrk(adjusted_size)) == -1) {
        return NULL;
    }

    return (void*)bp;
}

int mm_init(void)
{
    /* 빈 힙 초기화*/
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void*)-1) {
        return -1;
    }
    int list;
    for (list = 3; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }

    PUT(heap_listp, 0);
    PUT(heap_listp + WSIZE, PACK(2*WSIZE, 1));
    PUT(heap_listp + 2*WSIZE, PACK(2*WSIZE, 1));
    PUT(heap_listp + 3*WSIZE, PACK(0, 1));
    heap_listp += 2*WSIZE;

    return 0;
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

// size_t add_class;
static void *find_fit(size_t asize, int exp) {
    if (segregated_free_lists[exp] == NULL) {               
        return NULL;
    }

    // 안 비어있으면 해당 free 블록에 넣기
    return segregated_free_lists[exp];
}

// bp에다가 adjust_size만큼의 메모리를 할당받는다.
static void place(int exp) {
    list_remove(exp);
}

void *mm_malloc(size_t size)
{
    size_t adjusted_size;
    size_t extend_size;
    char* bp;
    int exp;
    // 의심스러운 요청을 무시한다.
    if (size == 0) {
        return NULL;
    }

    // 헤더,푸터, 정렬 요구사항대로 블록 사이즈를 조절한다.
    if (size <= DSIZE) {
        adjusted_size = 2 * DSIZE; // 푸터,헤더 무조건 추가(1더블워드: 헤더+푸터, 1더블워드: 페이로드+패딩)
        exp = 4;
    }

    // 더블워드보다 더 크면
    else {
        exp = get_exp(size);
        // 할당할 사이즈 = 더블워드 * (필요한 개수 = ) 
        adjusted_size = (1 << exp);
    }

    // free list에서 asize만큼의 자유 공간을 찾았으면 배치
    if ((bp = find_fit(adjusted_size, exp)) != NULL) {
        place(exp);
        return bp;
    }

    // 못찾았다.
    extend_size = MAX(adjusted_size, CHUNKSIZE);
    if ((bp = extend_heap(extend_size/WSIZE)) == NULL) {
        return NULL;
    }

    char* temp_bp = bp;

    size_t cls_size = 1<<exp;
    
    // 새로 공급받은 크기를 bp부터 나누어서 헤드에 연결하기
    
    for (temp_bp = bp; temp_bp < bp + extend_size; temp_bp += cls_size) {
        PUT(temp_bp, temp_bp + cls_size);
        list_add(temp_bp);
    }

    void* res = segregated_free_lists[exp];
    list_remove(exp);
    return res;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    list_add(bp);
}





/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    int a = ALIGN(sizeof(size_t));
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - WSIZE) - 1; // oldptr은 payload를 가리키고, 헤더를 가려면 -4 해야함, 여기엔 할당비트 포함되어 있으므로 -1 해줘서 해당 할당블록의 크기를 구함 
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
} 













