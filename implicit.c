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
static void *extend_heap(size_t);
static void *coalesce(void*);
static void *next_fit(size_t);
static void *best_fit(size_t);

static char* heap_listp; // 항상 prologue block을 가리키는 포인터
static char* last_bp; // next_fit 함수에서 제일 최근에 검색한 free 블록을 가리키는 포인터


/* 
 * mm_init - initialize the malloc package.
 */
// 힙 초기화 함수
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){ // heap_listp에 4word 만큼 메모리를 확장한다. padding, prologue(header, footer), epilogue를 위한 공간을 할당한다.
        return -1;
    }
    PUT(heap_listp, 0); // heap_listp가 가리키는 word에 0 저장 (제일 처음 padding영역을 할당)
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더를 1word 할당하고 값을 넣는다.
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // 프롤로그 풋터를 1word 할당하고 값을 넣는다.
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // 에필로그 헤더를 1word 할당하고 값을 넣는다.
    heap_listp += 2*WSIZE;

    // 2가지 다른 경우에 호출된다.
    // (1) 힙이 초기화 될때 (2) mm_malloc이 적당한 맞춤 fit을 찾지 못했을 때
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    last_bp = heap_listp; // next_fit bp

    return 0;
}

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

 static void *coalesce(void* bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 정보
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 정보
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈

    if (prev_alloc && next_alloc) { // case1. 이전 불록, 다음 블록이 모두 할당되었을 때
        last_bp = bp;
        return bp;
    }
    else if (prev_alloc && !next_alloc) { // case2. 이전 블록은 할당, 다음 블록이 가용상태일 때
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) { // case3. 이전 블록은 가용, 다음 블록이 할당 상태일 때
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else { // 이전 블록과 다음 블록 모두 가용상태일 때
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    last_bp = bp;
    return bp;
 }

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

// size 바이트의 메모리 블록을 요청
void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1){
    //     return NULL;
    // }
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

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
    
    if((bp = next_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize) {
    void* bp = heap_listp;
    
    while (GET_SIZE(HDRP(bp)) != 0) {
        bp = NEXT_BLKP(bp);
        if (GET_SIZE(HDRP(bp)) >= asize && GET_ALLOC(HDRP(bp)) == 0) {
            return bp;
        }
    }
    return NULL;
    
}

static void* next_fit(size_t asize) {
    char* bp = last_bp;

    while (GET_SIZE(HDRP(bp)) != 0) {
        bp = NEXT_BLKP(bp);
        if (GET_SIZE(HDRP(bp)) >= asize && GET_ALLOC(HDRP(bp)) == 0) {
            last_bp = bp;
            return bp;
        }
    }

    bp = heap_listp;
    
    while (bp < last_bp) {
        bp = NEXT_BLKP(bp);
        if (GET_SIZE(HDRP(bp)) >= asize && GET_ALLOC(HDRP(bp)) == 0) {
            last_bp = bp;
            return bp;
        }
    }
    return NULL;
}

static void* best_fit(size_t asize) {
    char* bp = heap_listp;
    char* result_bp = NULL;
    int min_difference = 20*(1 << 20);

    while (GET_SIZE(HDRP(bp)) != 0) {
        bp = NEXT_BLKP(bp);
        if (GET_SIZE(HDRP(bp)) >= asize && GET_ALLOC(HDRP(bp)) == 0 && GET_SIZE(HDRP(bp)) < min_difference) {
            min_difference = GET_SIZE(HDRP(bp));
            result_bp = bp;
            if (GET_SIZE(HDRP(bp)) == asize) {
                return result_bp;
            }
        }
    }
    return result_bp;
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    // 가용 블럭이 분할이 될 때
    if(csize - asize >= 2*DSIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize , 0));
        PUT(FTRP(bp), PACK(csize-asize , 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    
    // 헤더와 풋터를 0으로 할당하고 coalesce를 호출하여 가용 메모리를 이어준다.
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// void *mm_realloc(void *ptr, size_t size)
// {   
//     void *oldptr = ptr;
//     void *newptr;
//     size_t copySize;
    
//     newptr = mm_malloc(size);
//     if (newptr == NULL)
//       return NULL;
//     // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
//     copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
//     if (size < copySize)
//       copySize = size;
//     memcpy(newptr, oldptr, copySize); // 두번째 인자에 있는 원본을 세번째 인자만큼의 길이만큼 복사해서 첫번째 인자에 붙여 넣는 함수
//     mm_free(oldptr);
//     return newptr;
// }

/*
   기존에 malloc으로 동적 할당된 메모리 크기를 변경시켜주는 함수
   현재 메모리에 bp가 가르키는 사이즈를 할당한 만큼 충분하지 않다면 메모리의 다른 공간의 기존 크기의 공간 할당 + 기존에 있던 데이터를 복사한 후 추가로 메모리 할당
*/
void *mm_realloc(void *bp, size_t size) {
    size_t old_size = GET_SIZE(HDRP(bp));
    size_t new_size = size + (2 * WSIZE);   // 2*WISE는 헤더와 풋터
    // new_size가 old_size보다 작거나 같으면 기존 bp 그대로 사용
    if (new_size <= old_size) {
        return bp;
    }
    // new_size가 old_size보다 크면 사이즈 변경
    else {
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t current_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        // next block이 가용상태이고 old, next block의 사이즈 합이 new_size보다 크면 그냥 그거 바로 합쳐서 쓰기
        if (!next_alloc && current_size >= new_size) {
            PUT(HDRP(bp), PACK(current_size, 1));
            PUT(FTRP(bp), PACK(current_size, 1));
            return bp;
        }
        // 아니면 새로 block 만들어서 거기로 옮기기
        else {
            void *new_bp = mm_malloc(new_size);
            place(new_bp, new_size);
            memcpy(new_bp, bp, new_size);  // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수(old_bp로부터 new_size만큼의 문자를 new_bp로 복사해라!)
            mm_free(bp);
            return new_bp;
        }
    }

}
