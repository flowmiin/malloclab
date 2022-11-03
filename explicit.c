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
    "1team",
    /* First member's full name */
    "SUMIN YOO",
    /* First member's email address */
    "ysm2706@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};


#define ALIGNMENT 8

#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define MINIMUM 16 // 최소 블록 사이
#define PREC_FREEP(bp) (*(void**)(bp)) // bp의 이전 블록을 가리킨다.
#define SUCC_FREEP(bp) (*(void**)(bp + WSIZE)) // bp의 다음 블록을 가리킨다.

#define WSIZE 4 // 워드의 크기, header와 footer의 사이즈(4bytes)
#define DSIZE 8 // 더블 워드의 크기(8Bytes)
#define CHUNKSIZE (1<<12) // 확장하는 힙의 크기
#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc)) // header와 footer에 저장할 수 있는 값을 리턴
#define GET(p) (*(unsigned int* )(p)) // p가 참조하는 블록의 값을 읽어서 리턴, p는 (void *)형인데 역참조가 불가능하여 형변환한다.
#define PUT(p, val) (*(unsigned int* )(p) = (val)) //p가 가리키는 워드에 val 저장

#define GET_SIZE(p) (GET(p) & ~0x7) // 주소 p에 있는 header 또는 footer에 저장된 블록size 리턴, 7을 비트연산 not한 후 p의 주소와 &연산 한다.
#define GET_ALLOC(p) (GET(p) & 0x1) // heder 또는 footer의 할당 비트 리턴

#define HDRP(bp) ((char *)(bp) - WSIZE) // 블록헤더를 가리키는 포인터 리턴, bp(payload의 시작 주소)에서 1word 만큼 앞으로 주소 이동
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // footer를 가리키는 포인터 리턴

#define NEXT_BLKP(bp) ((char* )(bp) + GET_SIZE(((char* )(bp) - WSIZE))) // 다음 블록의 블록 포인터를 리턴, bp에 블록 사이즈 만큼 더해서 주소를 옮기면 다음 블록으로 이동
#define PREV_BLKP(bp) ((char* )(bp) - GET_SIZE(((char* )(bp) - DSIZE))) // 이전 블록의 블록 포인터를 리턴, bp에서 이전 푸터의 size만큼 빼주면 이전 블록의 bp로 이동

static void place(void *, size_t);
static void *find_fit(size_t);
static void* next_fit(size_t);
static void* best_fit(size_t);
static void *extend_heap(size_t);
static void *coalesce(void*);
void putFreeBlock(void* );
void removeBlock(void* );

static char* heap_listp = NULL; // heap(가용 리스트)을 가리키는 포인터
static char* free_listp = NULL; // free list의 제일 처음 블록을 가리키는 포인터
static char* last_freep = NULL; // 마지막으로 가용 리스트를 검색한 위치를 가리키는 포인터


// 힙 초기화 함수
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1){ // heap_listp에 6word 만큼 메모리를 확장한다. padding, prologue(header, footer), prec, succ, epilogue를 위한 공간을 할당한다.
        return -1;
    }
    PUT(heap_listp, 0); // heap_listp가 가리키는 word에 0 저장 (제일 처음 padding영역을 할당)
    PUT(heap_listp + (1*WSIZE), PACK(MINIMUM, 1)); // 프롤로그 헤더를 1word 할당하고 2*DSIZE로 값을 넣는다.
    PUT(heap_listp + (2*WSIZE), NULL); // PREC(조상블록)에 NULL 값 넣음
    PUT(heap_listp + (3*WSIZE), NULL); // SUCC(자손블록)에 NULL 값 넣음 
    PUT(heap_listp + (4*WSIZE), PACK(MINIMUM, 1)); // 프롤로그 풋터를 1word 할당하고 2*DSIZE로 값을 넣는다.
    PUT(heap_listp + (5*WSIZE), PACK(0, 1)); // 에필로그 헤더를 1워드 할당하고 0을 넣는다.

    free_listp = heap_listp + (2*WSIZE); // free_listp를 탐색의 시작점으로 둔다.
    last_freep = free_listp; // 가용 리스트를 검색한 위치를 시작점으로 둔다.

    // 힙을 CHUNKSIZE 바이트로 확장한다.
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

// 힙을 늘려주는 함수
static void *extend_heap(size_t words) {
    char* bp;
    size_t size;

    // 요청한 크기를 2워드의 배수로 반올림 하여 그 후에 추가적인 힙 공간 요청
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0)); // 새로운 블록 헤드를 만든다.
    PUT(FTRP(bp), PACK(size, 0)); // 새로운 블록 풋터를 만든다.
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새로운 블록 뒤에 에필로그 헤더를 만든다.

    return coalesce(bp); // case에 따라 가용 블록을 통합하기 위해 coalesce 호출
 }

// 가용 블록을 합쳐주는 함수
static void *coalesce(void* bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 가용 정보
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 가용 정보
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈

    if (prev_alloc && next_alloc) { // case1. 이전 불록, 다음 블록이 모두 할당되었을 때
        putFreeBlock(bp); // free 리스트에 넣어준다.
        return bp;
    }
    else if (prev_alloc && !next_alloc) { // case2. 이전 블록은 할당, 다음 블록이 가용상태일 때
        removeBlock(NEXT_BLKP(bp)); // free 상태인 다음 블록을 free 리스트에서 제거한다.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) { // case3. 이전 블록은 가용, 다음 블록이 할당 상태일 때
        removeBlock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else { // 이전 블록과 다음 블록 모두 가용상태일 때
        removeBlock(NEXT_BLKP(bp));
        removeBlock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    putFreeBlock(bp);
    return bp;
 }
 
// size 바이트 만큼의 메모리 블록을 요청
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0) {
        return NULL;
    }
    
    if(size <= DSIZE) { // 최소 16바이트 크기의 블록을 할당
        asize = 2*DSIZE;
    }
    else { // 8의 배수로 블록의 크기 조정
        asize = DSIZE*((size+(DSIZE) + (DSIZE-1)) / DSIZE);
    }
    
    // 가용 블록을 가용 리스트에서 검색하고 할당기는 요청한 블록을 가용 리스트에 배치한다.
    if((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    // 요청한 블록의 크기에 맞는 가용 블록 찾지 못하면 새로운 가용 블록으로 확장하고 배치한다.
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

// 요청받은 블록을 할당하기 위해 요청 사이즈에 맞는 가용 블록을 찾는 함수
static void* find_fit(size_t asize){
    void* bp = free_listp;
    
    while (GET_ALLOC(HDRP(bp)) != 1) {
        if (GET_SIZE(HDRP(bp)) >= asize) {
            return bp;
        }
        bp = SUCC_FREEP(bp);
    }
    return NULL;

}

static void* next_fit(size_t asize) {
    char* bp = last_freep;

    while(GET_ALLOC(HDRP(bp)) != 1) {
        if (GET_SIZE(HDRP(bp)) >= asize) {
            last_freep = bp;
            return bp;
        }
        bp = SUCC_FREEP(bp);
    }

    bp = free_listp;
    while(bp < last_freep) {
        if (GET_SIZE(HDRP(bp)) >= asize) {
            last_freep = bp;
            return bp;
        }
        bp = SUCC_FREEP(bp);
    }
    return NULL;
}

static void* best_fit(size_t asize) {
    void* bp = free_listp;
    void* result_bp = NULL;
    int min_difference = 1 << 30;

    
    while (GET_ALLOC(HDRP(bp)) != 1) {
        if (GET_SIZE(HDRP(bp)) >= asize && min_difference > GET_SIZE(HDRP(bp)) - asize) {
            min_difference = GET_SIZE(HDRP(bp)) - asize;
            result_bp = bp;
            if (min_difference == 0) {
                return result_bp;
            }
        }
        bp = SUCC_FREEP(bp);
    }
    return result_bp;
}

// free 블록을 할당 블록으로 바꿔주는 함수
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    removeBlock(bp);
    // 가용 블록이 분할 될 때
    if(csize - asize >= 2*DSIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize , 0));
        PUT(FTRP(bp), PACK(csize-asize , 0));
        putFreeBlock(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

// 새로 생성된 free 블록을 free list의 첫 부분에 넣는다
void putFreeBlock(void* bp) {
    PREC_FREEP(bp) = NULL;
    SUCC_FREEP(bp) = free_listp;
    PREC_FREEP(free_listp) = bp;
    free_listp = bp;
    last_freep = bp;
}

// 할당되는 free 블록을 free list에서 제거한다
void removeBlock(void* bp) {
    if (bp == free_listp) {
        PREC_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
        last_freep = free_listp;
    }
    else {
        PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
        SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
        last_freep = bp;
    }
}

void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    
    // 헤더와 풋터를 0으로 할당하고 coalesce를 호출하여 가용 메모리를 이어준다.
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

void *mm_realloc(void *ptr, size_t size)
{   
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize); // 두번째 인자에 있는 원본을 세번째 인자만큼의 길이만큼 복사해서 첫번째 인자에 붙여 넣는 함수
    mm_free(oldptr);
    return newptr;
}
