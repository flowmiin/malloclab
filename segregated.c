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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


/*
 * Constants and macros
 */
#define WSIZE 4                     // word size in bytes
#define DSIZE 8                     // double word size in bytes
#define INITCHUNKSIZE (1<<6)        // 
#define CHUNKSIZE (1<<12)           // page size in bytes

#define LISTLIMIT 20                // number of segregated lists

#define MAX(x, y) ((x) > (y) ? (x) : (y)) 
#define MIN(x, y) ((x) < (y) ? (x) : (y)) 

/* Pack size and allocation bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)            (*(unsigned int *)(p))
#define PUT(p, val)       (*(unsigned int *)(p) = (val))


/* Store predecessor or successor pointer for free blocks */
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

/* Read the size and allocation bit from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)


/* Address of block's header and footer */
#define HDRP(ptr) ((char *)(ptr) - WSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

/* Address of next and previous blocks */
#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))
#define PREV_BLKP(ptr) ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))

/* Address of free block's predecessor and successor entries */
#define PRED_PTR(ptr) ((char *)(ptr)) // ptr의 PRED 블록 
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE) // ptr의 SUCC 블록

/* Address of free block's predecessor and successor on the segregated list */
#define PRED(ptr) (*(char **)(ptr)) // ptr의 이전 블록을 가리킴
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr))) // ptr의 다음 블록을 가리킴


void *segregated_free_lists[LISTLIMIT]; 


static void *extend_heap(size_t size);
static void *coalesce(void *ptr);
static void *place(void *ptr, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);


// 힙의 크기를 늘리는 함수
static void *extend_heap(size_t size)
{
    void *ptr;                   
    size_t asize;
    
    asize = ALIGN(size);
    
    if ((ptr = mem_sbrk(asize)) == (void *)-1)
        return NULL;
    
    // 헤더와 풋터를 설정
    PUT(HDRP(ptr), PACK(asize, 0));  
    PUT(FTRP(ptr), PACK(asize, 0));   
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); 
    insert_node(ptr, asize);

    return coalesce(ptr);
}

// 분리 가용 리스트안에 free블록을 연결하는 함수
static void insert_node(void *ptr, size_t size) {
    int list = 0;
    void *succ_ptr = ptr;
    void *pred_ptr = NULL;
    
    // 요청한 블록의 크기에 맞는 분리 가용 리스트를 찾는 과정
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
    
    // free 블록의 크기를 오름차순으로 정렬하기 위해서 반복문을 돌린다. 
    succ_ptr = segregated_free_lists[list];
    while ((succ_ptr != NULL) && (size > GET_SIZE(HDRP(succ_ptr)))) {
        pred_ptr = succ_ptr;
        succ_ptr = SUCC(succ_ptr);
    }
    
    // pred와 succ를 설정하는 과정
    if (succ_ptr != NULL) {
        if (pred_ptr != NULL) { // 분리 가용 리스트안에 있는 제일 작은 free 블록의 크기 < size < 분리 가용 리스트안에 있는 제일 큰 free 블록의 크기 일 때
            SET_PTR(SUCC_PTR(ptr), succ_ptr);
            SET_PTR(PRED_PTR(succ_ptr), ptr);
            SET_PTR(PRED_PTR(ptr), pred_ptr);
            SET_PTR(SUCC_PTR(pred_ptr), ptr);
        } else { // 분리 가용 리스트 안에 있는 제일 작은 free 블록의 크기 > size 일 때
            SET_PTR(SUCC_PTR(ptr), succ_ptr);
            SET_PTR(PRED_PTR(succ_ptr), ptr);
            SET_PTR(PRED_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr; // root를 새로 삽입한 free블록으로 변경
        }
    } else {
        if (pred_ptr != NULL) { // 분리 가용 리스트안에 있는 모든 free 블록의 크기보다 더 큰 free 블록을 연결할 때
            SET_PTR(SUCC_PTR(ptr), NULL);
            SET_PTR(PRED_PTR(ptr), pred_ptr);
            SET_PTR(SUCC_PTR(pred_ptr), ptr);
        } else { // 분리 가용 리스트에 처음 free블록을 연결할 때
            SET_PTR(SUCC_PTR(ptr), NULL);
            SET_PTR(PRED_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr; // root를 새로 삽입한 free블록으로 변경
        }
    }
    return;
}


// 분리 가용 리스트에서 free블록을 삭제하는 함수
static void delete_node(void *ptr) {
    int list = 0;
    size_t size = GET_SIZE(HDRP(ptr));
    
    // 블록의 크기에 맞는 분리 가용 리스트를 선택하는 과정
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
    
    if (SUCC(ptr) != NULL) {
        if (PRED(ptr) != NULL) { // 조상, 자손과 연결된 free블록을 분리 가용 리스트에서 삭제할 때
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
        } else { // 분리 가용 리스트의 root free블록을 삭제할 때 (자손은 있음)
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL);
            segregated_free_lists[list] = SUCC(ptr);
        }
    } else {
        if (PRED(ptr) != NULL) { // 분리 가용 리스트의 제일 마지막 free블록을 삭제할 때
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
        } else { // 분리 가용 리스트에 한 개 밖에 없는 free블록을 삭제할 때
            segregated_free_lists[list] = NULL;
        }
    }
    
    return;
}

// free 리스트끼리 합치는 함수
static void *coalesce(void *ptr)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    if (prev_alloc && next_alloc) { // case1. 이전블록과 다음블록이 모두 할당된 블록일 때
        return ptr;
    }
    else if (prev_alloc && !next_alloc) { // case2. 이전블록은 할당, 다음블록은 가용 블록일 때
        delete_node(ptr);
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) { // case3. 이전블록은 가용, 다음블록은 할당 블록일 때
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    } else { // case4. 이전블록과 다음블록이 모드 가용 블록일 때
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    
    insert_node(ptr, size);
    
    return ptr;
}


// free 블록을 할당 블록으로 바꿔주는 함수
static void *place(void *ptr, size_t asize)
{
    size_t ptr_size = GET_SIZE(HDRP(ptr)); // 가용 블록의 크기
    size_t remainder = ptr_size - asize; // 가용 블록의 크기 - 할당할 블록의 크기
    
    delete_node(ptr);
    
    
    if (remainder <= DSIZE * 2) { // 가용 블록을 분할 할 수 없다면
        PUT(HDRP(ptr), PACK(ptr_size, 1));
        PUT(FTRP(ptr), PACK(ptr_size, 1)); 
    }
    
    else if(asize >= 100) { // 할당할 블록의 크기가 100 이상이면
        PUT(HDRP(ptr), PACK(remainder, 0)); // 가용 블록을 앞에 위치시킨다.
        PUT(FTRP(ptr), PACK(remainder, 0));
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(asize, 1)); // 할당 블록을 뒤에 위치시킨다.
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(asize, 1));
        insert_node(ptr, remainder); // 가용 블록을 분할 가용 리스트에 연결시킨다.
        return NEXT_BLKP(ptr);
        
    }
    
    else {
        PUT(HDRP(ptr), PACK(asize, 1)); // 할당 블록을 앞에 위치시킨다.
        PUT(FTRP(ptr), PACK(asize, 1)); 
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(remainder, 0)); // 가용 블록을 뒤에 위치시킨다.
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(remainder, 0));
        insert_node(NEXT_BLKP(ptr), remainder);
    }
    return ptr;
}


int mm_init(void)
{
    int list; // 분리 가용 리스트의 인덱스 값
    char *heap_start; // 힙의 시작점
    
    // 분리 가용 리스트들을 NULL로 초기값 설정
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }
    
    // 비어있는 힙에 메모리 할당
    if ((long)(heap_start = mem_sbrk(4 * WSIZE)) == -1)
        return -1;
    
    PUT(heap_start, 0); // padding 블록
    PUT(heap_start + (1 * WSIZE), PACK(DSIZE, 1)); // prologue header
    PUT(heap_start + (2 * WSIZE), PACK(DSIZE, 1)); // prologue footer
    PUT(heap_start + (3 * WSIZE), PACK(0, 1));     // epilogue header
    
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;
    
    return 0;
}


void *mm_malloc(size_t size)
{
    size_t asize; // 할당할 블록 사이즈
    size_t extendsize;  // Amount to extend heap if no fit
    void *ptr = NULL;   // Pointer
    int list = 0;       // List counter
    
    /* Filter invalid block size */
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include boundary tags and alignment requirements */
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = ALIGN(size+DSIZE);
    }
    
    /* Select a free block of sufficient size from segregated list */
    size_t searchsize = asize;
    while (list < LISTLIMIT) {
        if ((list == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != NULL))) { // 할당할 블록 크기에 맞는 분리 가용 리스트를 찾았거나 마지막 리스트 일 때
            ptr = segregated_free_lists[list];

            while ((ptr != NULL) && (asize > GET_SIZE(HDRP(ptr))))
            {
                ptr = SUCC(ptr);
            }
            if (ptr != NULL) // 가용 블록을 찾지 못 했을 때
                break;
        }
        
        searchsize >>= 1;
        list++;
    }
    
    /* Extend the heap if no free blocks of sufficient size are found */
    // 가용 블록을 찾지 못하면 힙의 크기를 늘려준다.
    if (ptr == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);
        
        if ((ptr = extend_heap(extendsize)) == NULL)
            return NULL;
    }
    
    /* Place the block */
    ptr = place(ptr, asize);
    
    
    /* Return pointer to newly allocated block */
    return ptr;
}


void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    
    insert_node(ptr, size);
    
    coalesce(ptr);
    
    return;
}


//블록의 사이즈를 변경하는 함수
void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr = ptr;    /* Pointer to be returned */
    size_t new_size = size; /* Size of new block */
    int current_size = GET_SIZE(HDRP(ptr));
    int add_size = 0;          /* Adequacy of block sizes */
    int extendsize;         /* Size of heap extension */
    
    // Ignore size 0 cases
    if (size == 0)
        return NULL;
    
    // Align block size
    if (new_size <= DSIZE) {
        new_size = 2 * DSIZE;
    } else {
        new_size = ALIGN(size+DSIZE);
    }

    // 다음 블록이 가용 블록 or 다음 블록이 epilogue 블록일 때
    
    if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
        add_size = current_size + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;
        if (add_size < 0) {
            extendsize = MAX(-add_size, INITCHUNKSIZE);
            if (extend_heap(extendsize) == NULL)
                return NULL;
            add_size += extendsize;
        }

        delete_node(NEXT_BLKP(ptr));

        // Do not split block
        PUT(HDRP(ptr), PACK(new_size + add_size, 1));
        PUT(FTRP(ptr), PACK(new_size + add_size, 1)); 
    }
    
    else {
        new_ptr = mm_malloc(new_size + INITCHUNKSIZE - DSIZE);
        memcpy(new_ptr, ptr, MIN(size, new_size));
        mm_free(ptr);
    }

    return new_ptr;
}
