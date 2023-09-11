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

// 현재 블록 padding 주소 - 이전 블록 크기 = 이전 블록 bp
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
#define MIN_BLOCK_SIZE 8
static char* mem_heap; // 힙의 첫 바이트주소
static char* mem_brk; // 힙의 마지막 바이트주소 + 1
static char* mem_max_addr; // 가능한 최대 힙 주소 + 1
static char* break_point = NULL; // next_fit 용 bp
/* 
 * mm_init - initialize the malloc package.
 */

static void* coalesce(void* bp) {
    // 주변 블록의 할당여부 구하기 
    size_t is_prev_allocated = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 할당여부 구하기
    size_t is_next_allocated = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 할당여부 구하기
    size_t size = GET_SIZE(HDRP(bp));
    
    // 이전, 다음 블록 모두 할당되어 있었으면 할거 없으니 그냥 bp 반환
    if (is_prev_allocated && is_next_allocated) {
        return bp;
    }

    // 이전 블록은 할당, 다음블록은 free
    else if (is_prev_allocated && !is_next_allocated) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // 이전 블록은 free, 다음 블록은 할당
    else if (!is_prev_allocated && is_next_allocated) {
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // 양쪽 둘다 비할당인 경우
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    break_point = bp;
    return bp;
}

static void* extend_heap(size_t words) {
    char* bp;
    size_t size;

    /* 정렬을 유지시키기 위해 짝수만큼 할당 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // 힙 크기 키워주는 mem_sbrk 호출하고 -1 나오면 실패라서 NULL 리턴
    // bp는 이전 ㄹ
    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

    /* 프리블록 헤더푸터와 에필로드 헤더 초기화 */
    PUT(HDRP(bp), PACK(size, 0)); // 헤더위치에 사이즈랑 free 상태 넣기
    PUT(FTRP(bp), PACK(size, 0)); // 푸터위치에 사이즈랑 free 상태 넣기
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 다음 블록(에필로그) 헤더에 사이즈0, 할당1 넣기

    // 이전 블록이 free면 병합시켜주기

    return coalesce((void*)bp);
}

int mm_init(void)
{
    /* 빈 힙 초기화*/
    if ((mem_heap = mem_sbrk(4 * WSIZE)) == (void*)-1) {
        return -1;
    }

    // 초기세팅: 총 4워드
    PUT(mem_heap, 0); // 힙 시작지점에 정렬용 패딩값 0 넣기, 1워드
    PUT(mem_heap + (1*WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더, 크기 = 1워드, 할당비트 = 1, 1워드
    PUT(mem_heap + (2*WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터, 크기 = 1워드, 할당비트 = 1, 1워드
    PUT(mem_heap + (3*WSIZE), PACK(0, 1)); // 에필로그 헤더, 크기 = 0, 할당비트 = 1, 1워드

    mem_heap += (2*WSIZE);
    break_point = mem_heap;

    /* 빈 힙을 CHUNKSIZE만큼 프리블록 만들어줌 */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        // printf("HI");
        return -1;
    }

    return 0;
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

static void* find_fit(size_t adjusted_size) {
    // getsize, getalloc, put
    // heap_listp를 돈다. 그러면서 할당비트를 체크하는데 1이면 넘기고 0이면 사이즈 체크해서 공간이 더크면 할당
    // 더 작으면 다음거
    // 다음거 가는법: 현재 헤더에 적혀있는 블록 크기값+ 현재 bp

    // 초기 mem_heap 위치= 프롤로그 블록의 페이로드 시작주소
    // char* temp_point = break_point;

    // 에필로그에 도달했을 때 탈출, 에필로그 도달조건: sz == 0 and is_alled = 1, 반대 = sz != 0 || is_alled != 1
    // if (break_point == NULL) {
    //     break_point = mem_heap;
    // }
    void *bp;
    

    for (bp = break_point; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (adjusted_size <= GET_SIZE(HDRP(bp)))) {
            break_point = bp;
            return bp;
        }
    }
    
    for (bp = mem_heap; bp != break_point; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (adjusted_size <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }

    return NULL;
}

// bp에다가 adjust_size만큼의 메모리를 할당받는다.
static void place(void *bp, size_t adjusted_size) {
    // 헤더, 푸터 만들고
    // bp는 현재 free block의 payload주소다. 따라서 header를 구해서 넣는데, size | 1을 해서 넣기
    size_t remained = GET_SIZE(HDRP(bp)) - adjusted_size;

    // 최소 블록 사이즈보다 할당하고도 남는 공간이 더 클 때,
    if (remained >= MIN_BLOCK_SIZE) {
        // 할당 블럭 헤더 푸터 만들고
        PUT(HDRP(bp), PACK(adjusted_size, 0x1));
        PUT(FTRP(bp), PACK(adjusted_size, 0x1));

        // 남는 free 블럭 헤더 푸터 만들기
        PUT(HDRP(NEXT_BLKP(bp)), PACK(remained, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(remained, 0));
        // break_point = NEXT_BLKP(bp);
    }
    // 
    else {
        //
        PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 0x1));
        PUT(FTRP(bp), PACK(GET_SIZE(HDRP(bp)), 0x1));
        // 더 작을 때, 다음 블록의 페이로드를 가리키게 함, 에필로그인 경우에는, 에필로그 헤더 이후 페이로드 주소부분을 가리키게 되서 힙을 벗어나지만, 이후 find함수 호출시 HDRP 매크로로 구할 때 wsize만큼 빼주므로 에필로그의 헤더에 접근할 수 있다.
        // break_point = NEXT_BLKP(bp);
    }
    break_point = bp;
}

void *mm_malloc(size_t size)
{
    size_t adjusted_size;
    size_t extend_size;
    char* bp;

    // 의심스러운 요청을 무시한다.
    if (size == 0) {
        return NULL;
    }

    // 헤더,푸터, 정렬 요구사항대로 블록 사이즈를 조절한다.
    if (size <= DSIZE) {
        adjusted_size = 2*DSIZE; // 푸터,헤더 무조건 추가(1더블워드: 헤더+푸터, 1더블워드: 페이로드+패딩)
    }

    // 더블워드보다 더 크면
    else {
        // 할당할 사이즈 = 더블워드 * (필요한 개수 = ) 
        adjusted_size = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    // free list에서 asize만큼의 자유 공간을 찾았으면 배치
    if ((bp = find_fit(adjusted_size)) != NULL) {
        // break_point = bp;
        place(bp, adjusted_size);
        return bp;
    }

    // 못찾았다.
    extend_size = MAX(adjusted_size, CHUNKSIZE);
    if ((bp = extend_heap(extend_size/WSIZE)) == NULL) {
        return NULL;
    }
    // break_point = bp;
    place(bp, adjusted_size);
    return bp;
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

// 개선가능: 크기 키울 할당된블록이 그 이후에 free 블록이 있을 경우
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    size_t cur_block_size = GET_SIZE(HDRP(ptr));

    if (size == cur_block_size) {
        return ptr;
    }

    // // 현재 블록에서 size만큼 뺀값이 최소 free블록 크기인 8보다 클 때  
    // if (cur_block_size - size >= MIN_BLOCK_SIZE) {
    //     // 헤더푸터 갱신하고
    //     PUT(HDRP(ptr), PACK(size, 1));
    //     PUT(FTRP(ptr), PACK(size, 1));
        
    //     // 다음블록 프리시키기
    //     PUT(HDRP(NEXT_BLKP(ptr)), PACK(cur_block_size - size, 0));
    //     PUT(FTRP(NEXT_BLKP(ptr)), PACK(cur_block_size - size, 0));

    //     // 병합 가능하면 하기
    //     coalesce(NEXT_BLKP(ptr));
    //     return ptr;
    // }

    // // 남은게 1 ~ 7인 경우
    // if (1 <= cur_block_size - size && cur_block_size - size <= 7) {
    //     return ptr;
    // }

    // size가 더 큼
    // 다음 블록이 free일 때,
    if (GET_ALLOC(HDRP(NEXT_BLKP(ptr))) == 0 && cur_block_size > size) {

        // 다음 free 블록 사이즈
        size_t next_block_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));

        // 더 추가해야할 양
        size_t remained = size - GET_SIZE(HDRP(ptr));
        // 다음 프리블록이 더 클 때,
        if (remained <= next_block_size) {
            // 남은 블록크기가 최소 프리블록 사이즈 이상일 때,
            if (MIN_BLOCK_SIZE <= next_block_size - remained) {
                // 헤드, 푸터 크기 변경
                PUT(HDRP(ptr), PACK(size, 1));
                PUT(FTRP(ptr), PACK(size, 1));

                // 다음 free블록 헤더 푸터 변경
                PUT(HDRP(NEXT_BLKP(ptr)), PACK(next_block_size - remained, 0));
                PUT(FTRP(NEXT_BLKP(ptr)), PACK(next_block_size - remained, 0));

                coalesce(NEXT_BLKP(ptr));
            }
            // 남은 블록 크기가 최소 사이즈보다 작을 때
            else {
                size_t cur_size = GET_SIZE(HDRP(ptr));
                size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));

                PUT(HDRP(ptr), PACK(cur_size + next_size, 1));
                PUT(FTRP(ptr), PACK(cur_size + next_size, 1));
            }

            return ptr;
        }
    }

    // 다음블록이 free블록이지만 작을 때 or 할당블록일 때는 새로 할당
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




















