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
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
 * mm_init - initialize the malloc package.
 */

#define WSIZE 4 // 헤더/푸터 크기
#define DSIZE 8 // 더블워드 크기(정렬 기준)
#define CHUNKSIZE (1<<12) // 힙 확장 기본 크기(4096 바이트)

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 맥스 함수

#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당비트를 1워드로 합친다.
#define GET(p) (*(unsigned int *)(p)) // 주소 p에서 1워드를 읽어오기
#define PUT(p, val) (*(unsigned int*)(p) = (val)) // 주소 p에 1워드를 쓰기

#define GET_SIZE(p) ((GET(p) & ~0x7)) // 주소 p에서 하위 3비트를 0으로 만듦 (부호비트)
#define GET_ALLOC(p) ((GET(p) & 0x1)) // 최하위 1비트만 읽기

#define HDRP(bp) ((char *)(bp) - WSIZE) // bp에서 4바이트 앞으로 (헤더 주소 읽기)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // bp + 블록크기 - 8B (푸터 주소 읽기)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // bp를 이용해 다음 블록의 페이로드 주소를 계산
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // bp를 이용해 이전 블록의 페이로드 주소를 계산

// 명시적 리스트를 위한 8바이트 포인터 매크로
#define GET_PTR(p) (*(char **)(p)) // 명시적 리스트를 위한 8바이트 포인터 매크로
#define PUT_PTR(p, val) ((*(char **)(p)) = (val))

// 가용 블록(bp)의 PRED/SUCC 포인터 주소를 계산
// 가용 블록의 페이로드(bp) 시작 지점이 PRED 포인터의 위치
#define PRED_PTR(bp) ((char *)(bp))
#define SUCC_PTR(bp) ((char *)(bp) + DSIZE)

// 가용 블록(bp) 의 PRED/SUCC 블록 포인터(주소값)를 가져온다.
#define GET_PRED(bp) ((GET_PTR(PRED_PTR(bp))))
#define GET_SUCC(bp) ((GET_PTR(SUCC_PTR(bp))))

static char* heap_listp;
static char* free_listp;

static char *extend_heap(size_t words);
static void *First_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void insert_node(void *bp);
static void remove_node(void *bp);

static void insert_node(void *bp)
{
    // 새 블록(bp)의 SUCC을 현재 head(free_listp)로 설정
    PUT_PTR(SUCC_PTR(bp), free_listp);
    
    // 리스트가 비어있지 않다면
    if (free_listp != NULL)
    {
        // 이전 head의 PRED를 새 블록(bp)으로 설정
        PUT_PTR(PRED_PTR(free_listp), bp);
    }

    // 새 블록(bp)의 PRED는 NULL로 설정(이제 head이므로)
    PUT_PTR(PRED_PTR(bp), NULL);

    // head 포인터(free_listp)를 새 블록(bp)로 갱신
    free_listp = bp;
}

static void remove_node(void* bp)
{
    void *prev_free = GET_PRED(bp); // bp의 이전 가용 블록
    void *next_free = GET_SUCC(bp); // bp의 다음 가용 블록

    if (prev_free) {
        // Case 1: bp가 Head가 아닐 때 (이전 노드가 있음)
        // (이전 블록) -> succ = (다음 블록)
        PUT_PTR(SUCC_PTR(prev_free), next_free);
    } else {
        // Case 2: bp가 Head일 때 (이전 노드가 없음)
        // free_listp(head) = (다음 블록)
        free_listp = next_free;
    }

    if (next_free) {
        // Case 3: bp가 Tail이 아닐 때 (다음 노드가 있음)
        // (다음 블록) -> pred = (이전 블록)
        PUT_PTR(PRED_PTR(next_free), prev_free);
    }
}

static char* extend_heap(size_t words)
{
    char *bp;
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    // return coalesce(bp); // (X) 이전 코드
    
    void *merged_bp = coalesce(bp); // ★ (수정) 
    insert_node(merged_bp);     // ★ (수정) 새 블록을 리스트에 삽입
    return merged_bp;
}

// First-fit
static void* First_fit(size_t asize)
{
    void* bp;

    // free_listp 부터 시작
    for (bp = free_listp;  bp != NULL; bp = GET_SUCC(bp))
    {
        // GET_SUCC(bp)를 통해 다음 가용 블록으로 점프
        // 사용 가능 가용 블록을 찾으면
        if (GET_SIZE(HDRP(bp)) >= asize)
        {
            return bp; // 즉시 검색을 중단하고 반환
        }
    }
    return NULL; // 끝까지 돌았는데 못 찾음
}

// * 가용 블록(bp)에 asize만큼을 배치하고,
//  * 남는 공간이 최소 블록 크기(16B) 이상이면 분할(split).
//  */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); 
    size_t remainder = csize - asize;  

    remove_node(bp); // (이것은 올바름) 할당할 블록을 리스트에서 제거

    if (remainder >= (3*DSIZE)) { 
        /* Case 1: 분할 (Splitting) */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        void* next_bp = NEXT_BLKP(bp); // ★ 1. 새 변수 이름 사용

        PUT(HDRP(next_bp), PACK(remainder, 0));
        PUT(FTRP(next_bp), PACK(remainder, 0));

        insert_node(next_bp); // ★ 2. 남은 조각을 리스트에 다시 삽입
    } 
    else { 
        /* Case 2: 분할 안 함 */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void* coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    char* prev_bp = PREV_BLKP(bp);
    char* next_bp = NEXT_BLKP(bp);

    if (prev_alloc && next_alloc) { /* Case 1 */
        return bp;
    }
    else if (prev_alloc && !next_alloc) { /* Case 2 */
        remove_node(next_bp); // ★ (추가) 합쳐질 블록을 리스트에서 제거
        size += GET_SIZE(HDRP(next_bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }
    else if (!prev_alloc && next_alloc) { /* Case 3 */
        remove_node(prev_bp); // ★ (추가) 합쳐질 블록을 리스트에서 제거
        size += GET_SIZE(HDRP(prev_bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(prev_bp), PACK(size, 0));
        bp = prev_bp; 
    }
    else { /* Case 4 */
        remove_node(prev_bp); // ★ (추가) 두 블록 모두 제거
        remove_node(next_bp);
        size += GET_SIZE(HDRP(prev_bp)) + GET_SIZE(FTRP(next_bp));
        PUT(HDRP(prev_bp), PACK(size, 0));
        PUT(FTRP(next_bp), PACK(size, 0));
        bp = prev_bp; 
    }
    return bp; // (최종 합쳐진 블록 반환)
}

int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1){
        return -1;
    }
    PUT(heap_listp, 0); // 주소 0에 4바이트 패딩을 두어서, 모든 페이로드가 8 바이트경계에 정렬되도록 한다.
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE,1)); // 프롤로그 헤더 블록 지정
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE,1)); // 프롤로그 푸터 블록 지정
    PUT(heap_listp + (3 * WSIZE), PACK(0,1)); // 에필로그 헤더 블록 지정
    heap_listp += (2 * WSIZE);

    free_listp = NULL;

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    
    return 0;
}

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    
    // coalesce(bp); // (X) 이전 코드
    insert_node(coalesce(bp)); // ★ (수정) 합쳐진 블록을 리스트에 삽입
}


/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* 조정된 블록 크기 (헤더/푸터/정렬 포함) */
    size_t extendsize; /* 힙 확장 크기 */
    char *bp;

    /* 1. 엉뚱한 요청 무시 */
    if (size == 0)
        return NULL;

    size_t min_block_size = 3 * DSIZE;

    /* 2. 크기 조정 (오버헤드 및 정렬 요구사항 포함) */
    if (size <= (min_block_size - DSIZE))
        asize = min_block_size; // 최소 블록 크기 24바이트
    else
        // 8바이트 오버헤드 + 8바이트 배수로 올림
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* 3. 가용 리스트 검색 (find_fit) */
    if ((bp = First_fit(asize)) != NULL) {
        place(bp, asize); // 배치 및 분할
        return bp;
    }

    /* 4. Fit을 못 찾음. 힙 확장 (extend_heap) */
    extendsize = MAX(asize, CHUNKSIZE); // 둘 중 큰 값으로 확장
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL; // 메모리 부족
    
    place(bp, asize); // 새 힙에 배치
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t old_block_size;
    size_t copySize;

    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    old_block_size = GET_SIZE(HDRP(oldptr));
    copySize = old_block_size - DSIZE; 

    if (size < copySize)
        copySize = size;

    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);

    return newptr;
}