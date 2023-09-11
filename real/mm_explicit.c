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
#define MIN_FREE_BLOCK_SIZE 16
static char* mem_heap; // 힙의 첫 바이트주소

/* 매크로 wrapper 함수 */
static size_t _get(p) {return GET(p);}
static void _put(p, val) {PUT(p, val);}
static int _get_size(p) {return GET_SIZE(p);}
static int _get_alloc(p) {return GET_ALLOC(p);}
static char* _hdrp(bp) {return HDRP(bp);}
static char* _ftrp(bp) {return FTRP(bp);}
static char* _next_blkp(bp) {return NEXT_BLKP(bp);}
static char* prev_blkp(bp) {return PREV_BLKP(bp);}

/* 
 * mm_init - initialize the malloc package.
 */
static char* head;
static char* tail;

static void* coalesce(void* bp) {
    // 주변 블록의 할당여부 구하기 
    size_t is_prev_allocated = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 할당여부 구하기
    size_t is_next_allocated = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 할당여부 구하기
    size_t size = GET_SIZE(HDRP(bp));
    
    // 이전, 다음 블록 모두 할당되어 있었으면 할거 없으니 그냥 bp 반환
    if (is_prev_allocated && is_next_allocated) {
        // 맨 앞에 연결

        char* temp = GET(head);
        PUT(bp, GET(head));
        PUT(bp + WSIZE, head + WSIZE);
        PUT(head, bp);
        PUT(temp + WSIZE, bp + WSIZE);
        
        return bp;
    }

    // 이전 블록은 할당, 다음블록은 free
    // bp가 맨앞
    else if (is_prev_allocated && !is_next_allocated) {
        // bp(할당해제될)블록의 다음 next주소값
        char* next_block = NEXT_BLKP(bp);

        // 다음 블록을 가리킴
        char* next_next_block = GET(next_block);

        // 이전 블록을 가리킴
        char* next_prev_block = GET(next_block + WSIZE);

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
        // 연결관계 변경
        // 헤드값: 프롤로그 next 주소
        
        // bp의 next칸에 head가 가리켰던 곳 넣기
        PUT(bp, GET(head));

        // bp의 prev는 프롤로그의 prev
        PUT(bp + WSIZE, head + WSIZE);

        // 이전 맨앞 노드의 prev는 bp의 prev주소값
        PUT(GET(head) + WSIZE, bp + WSIZE);

        // head 주소에는 bp 넣고
        PUT(head, bp);

        // 병합전 free블록의 연결관계 
        PUT(next_next_block + WSIZE, next_prev_block);
        PUT(next_prev_block - WSIZE, next_next_block);
    }

    // 이전 블록은 free, 다음 블록은 할당
    else if (!is_prev_allocated && is_next_allocated) {
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

        // 총 6가지 연결관계 재정립

        // bp블록의 next, prev 주소값 임시저장
        char* next_temp = GET(bp);
        char* prev_temp = GET(bp + WSIZE);
        
        // head 내용물 임시저장
        char* first = GET(head);

        // 헤드 내용물 변경
        PUT(head, bp);
        
        // bp블록의 next 변경
        PUT(bp, first);

        // bp블록의 prev 변경
        PUT(bp + WSIZE, head + WSIZE);

        // first 블럭의 prev 변경
        PUT(first + WSIZE, bp + WSIZE);

        // bp블록의 양 연결관계 변경
        PUT(next_temp + WSIZE, prev_temp);
        PUT(prev_temp - WSIZE, next_temp);
    }

    // 양쪽 둘다 비할당인 경우
    else {
        char* free_block1 = PREV_BLKP(bp);
        char* free_block2 = NEXT_BLKP(bp);

        char* free_block1_prev = GET(free_block1 + WSIZE);
        char* free_block1_next = GET(free_block1);

        char* free_block2_prev = GET(free_block2 + WSIZE);
        char* free_block2_next = GET(free_block2);

        
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

        /* 8가지 처리 */ 

        // bp의 next에 head가 가리켰던 주소 넣기
        PUT(bp, GET(head));

        // 기존 맨앞 노드의 prev에 새bp노드 넣기
        PUT(GET(head) + WSIZE, bp + WSIZE);

        // 헤드 가리키는 값 변경
        PUT(head, bp);

        // bp블럭 prev 가리키는 값 변경
        PUT(bp + WSIZE, head + WSIZE);

        /* 4가지 연결관계 변경 */ 
        
        PUT(free_block1_prev - WSIZE, free_block1_next);
        PUT(free_block1_next + WSIZE, free_block1_prev);

        PUT(free_block2_prev - WSIZE, free_block2_next);
        PUT(free_block2_next - WSIZE, free_block2_prev);
    }

    return bp;
}

static void* extend_heap(size_t words) {
    char* bp;
    size_t size;

    /* 정렬을 유지시키기 위해 짝수만큼 할당 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // 힙 크기 키워주는 mem_sbrk 호출하고 -1 나오면 실패라서 NULL 리턴
    // bp는 이전 힙 마지막 주소
    // tail은 이전 블록의 prev주소 가리킴
    char* temp = GET(tail); // temp: tail 이전 블록의 prev주소

    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }
    bp -= 3*WSIZE; // 3워드만큼 빼주어야 새롭게 만든 free block의 payload 주소이다.

    /* 프리블록 헤더푸터 초기화 */
    PUT(HDRP(bp), PACK(size, 0)); // 헤더위치에 사이즈랑 free 상태 넣기
    PUT(FTRP(bp), PACK(size, 0)); // 푸터위치에 사이즈랑 free 상태 넣기

    /* 에필로그 초기화 */ 
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 다음 블록(에필로그) 헤더에 사이즈0, 할당1 넣기
    PUT(FTRP(NEXT_BLKP(bp)), PACK(0, 1)); // 다음 블록(에필로그) 푸터에 사이즈0, 할당1 넣기

    tail = bp + size + WSIZE;

    PUT(temp - WSIZE, tail - WSIZE);
    PUT(tail, temp);
    // // 이전 tail값 저장(에필로그의 prev주소)
    // char* tail_temp = tail;
    // char* tail_prev_temp = GET(tail);
    
    // PUT(tail_temp)
    // // 에필로그 이전 블록의 next를 새 애필로그의 next주소로 변경
    // PUT(GET(tail_temp) - WSIZE, bp + size);
     
    // // 에필로그 next를 NULL로 변경
    // PUT(bp + size, NULL);

    // // 에필로그 prev를 이전블록의 prev주소로 변경
    // PUT(bp + size + WSIZE, tail_prev_temp);

    // // tail에 새 에필로그의 prev주소를 넣음.

    // /* free block을 앞에 넣기 */

    // // head는 프롤로그의 next담긴 주소다.
    // // next자리에 헤드주소에 담긴 next 넣기
    // PUT(bp, GET(head));

    // // prev자리에 헤드의 prev주소 넣기
    // PUT(bp + WSIZE, head + WSIZE);

    // // head의 next의 prev가 free다.
    // // head의 next 블록의 prev주소에는 free의 prev주소가 들어가야 한다.
    // PUT(GET(head) + WSIZE, bp + WSIZE);

    // // head의 next주소에는 free의 next주소를 가리키고 있어야 한다.
    // PUT(head, bp);


    // 이전 블록이 free면 병합시켜주기
    return coalesce((void*)bp);
}

int mm_init(void)
{
    /* 빈 힙 초기화*/
    // 정렬용 1워드 + 프롤로그 4워드 + 에필로그 4워드 = 9워드
    if ((mem_heap = mem_sbrk(9 * WSIZE)) == (void*)-1) {
        return -1;
    }

    // 초기세팅: 총 9워드

    // 주소 8배수 정렬용 1워드 블록
    PUT(mem_heap, 0);

    // 프롤로그 헤더 1블록
    PUT(mem_heap + (1*WSIZE), PACK(WSIZE * 4, 1)); 

    // 프롤로그 next 1블록
    // 에피소드 블록의 next주소를 넣기
    PUT(mem_heap + (2*WSIZE), mem_heap + 6*WSIZE);

    // 프롤로그 prev 1블록
    // NULL을 넣는다.
    PUT(mem_heap + (3*WSIZE), NULL); // 프롤로그 푸터, 크기 = 1워드, 할당비트 = 1, 1워드

    // 프롤로그 푸터 1블록
    PUT(mem_heap + (4*WSIZE), PACK(WSIZE * 4, 1));

    // 에필로그 헤더 1블록
    PUT(mem_heap + (5*WSIZE), PACK(WSIZE * 4, 1));

    // 에필로그 next 1블록
    // NULL 넣기
    PUT(mem_heap + (6*WSIZE), NULL);

    // 에필로그 prev 1블록
    // 프롤로그 블록의 prev 주소 넣기
    PUT(mem_heap + (7*WSIZE), mem_heap + 3*WSIZE);

    // 프롤로그 푸터 1블록
    PUT(mem_heap + (8*WSIZE), PACK(WSIZE * 4, 1));

    // head에 프롤로그의 next가 담긴 주소 넣기
    head = mem_heap + 2*WSIZE;
    
    // tail에 에필로그의 prev주소 넣기
    tail = mem_heap + 7*WSIZE;

    mem_heap += 2*WSIZE; // 프롤로그의 bp 가리킴

    /* 빈 힙을 CHUNKSIZE(4096B, 1024블록)만큼 프리블록 만들어줌 */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }

    return 0;
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

// head를 타고 들어가서 tail을 만나기 전까지 들어갈 수 있는 free를 찾는다.
// 찾으면 할당 및 병합
// head = 프롤로그의 next주소
static void* find_fit(size_t adjusted_size) {
    void *bp;
     
    // free 블록들만 돌기
    for (bp = GET(head); GET_SIZE(HDRP(bp)) != 0 ;bp = GET(bp)) {
        // free 크기 크면 넣을 수 있다.
        if (adjusted_size <= GET_SIZE(HDRP(bp))) {
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
    if (remained >= MIN_FREE_BLOCK_SIZE) {
        // cur 기준 다음, 이전블록 임시저장
        void* next_block = GET(bp);
        void* prev_block = GET(bp + WSIZE);

        // 할당 블럭 헤더 푸터 만들고
        PUT(HDRP(bp), PACK(adjusted_size, 0x1));
        PUT(FTRP(bp), PACK(adjusted_size, 0x1));

        // 남은 free 블럭 헤더 푸터 만들기
        PUT(HDRP(NEXT_BLKP(bp)), PACK(remained, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(remained, 0));

        // 남은 free 블럭 next, prev 만들기
        
        // next에 다음 블록의 next 주소
        PUT(NEXT_BLKP(bp), next_block);
        // prev에 이전 블록의 prev 주소
        PUT(NEXT_BLKP(bp) + WSIZE, prev_block);

        // 이전블록 next 연결 변경
        PUT(prev_block - WSIZE, NEXT_BLKP(bp));

        // 다음블록 prev 연결 변경
        PUT(next_block + WSIZE, NEXT_BLKP(bp) + WSIZE);
    }

    // 남는 공간 부족하면 다 먹고 연결 제거
    else {
        // cur 기준 다음, 이전블록 임시저장
        void* next_block = GET(bp);
        void* prev_block = GET(bp + WSIZE);

        // 헤더 푸터 넣고
        PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 0x1));
        PUT(FTRP(bp), PACK(GET_SIZE(HDRP(bp)), 0x1));

        // 이전 블록의 next를 다음 블록의 next주소로 함
        PUT(prev_block - WSIZE, next_block);

        // 다음 블록의 prev를 이전 블록의 prev주소로 함
        PUT(next_block + WSIZE, prev_block);
    }
}

void *mm_malloc(size_t size)
{
    size_t adjusted_size;
    size_t extend_size;
    char* bp;

    // 의심스러운 요청을 무시한다.
    if (size <= 0) {
        return NULL;
    }

    // 헤더,푸터, 정렬 요구사항대로 블록 사이즈를 조절한다.
    if (size <= 2 * DSIZE) {
        adjusted_size = 4*DSIZE; // 푸터,헤더 무조건 추가(1더블워드: 헤더+푸터, 1더블워드: 페이로드+패딩)
    }

    // 더블워드보다 더 크면
    else {
        // 할당할 사이즈 = 더블워드 * (필요한 개수 = ) 
        adjusted_size = (2 * DSIZE) * ((size + (2 * DSIZE) + (2 * DSIZE - 1)) / (2 * DSIZE));
    }

    // free list에서 asize만큼의 자유 공간을 찾았으면 배치
    if ((bp = find_fit(adjusted_size)) != NULL) {
        place(bp, adjusted_size);
        return bp;
    }

    // 못찾았다.
    extend_size = MAX(adjusted_size, CHUNKSIZE);
    if ((bp = extend_heap(extend_size/WSIZE)) == NULL) {
        return NULL;
    }
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

    // 링크드리스트 맨앞에 연결
    // char* temp = GET(head);
    // PUT(bp, GET(head));
    // PUT(bp + WSIZE, head + WSIZE);
    // PUT(head, bp);
    // PUT(temp + WSIZE, bp + WSIZE);
    coalesce(bp);
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



















