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

static char* heap_listp;

static char *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);

static char* extend_heap(size_t words){
    char *bp;
    size_t size;
    // 정렬(aligment)를 유지하기 위해 요청된 크기(words)를 짝수 워드로 올림한다.
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL; // sbrk 실패시 (메모리 부족)
    }

    // (새로 받은 공간에) 가용 블록  헤더/푸터를 초기화 한다.
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // (힙의 맨 끝에) 새로운 에필로그 헤더를 초기화 한다.
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    // 만약 이전 블록이 가용 상태였다면, 두 블록을 연결한다.
    return coalesce(bp);
}

// first fit
static void* find_fit(size_t asize)
{
    void *bp; // 블럭 포인터
    
    // heap_listp는 프롤로그 블록을 가리킨다.
    // 프롤로그의 다음 블록(실제 첫 블록)부터 검색 시작.
    for (bp = NEXT_BLKP(heap_listp); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {

        if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= asize)){
            return bp;
        }
    }
    return NULL;
}

// * 가용 블록(bp)에 asize만큼을 배치하고,
//  * 남는 공간이 최소 블록 크기(16B) 이상이면 분할(split).
//  */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 가용 블록의 크기
    size_t remainder = csize - asize;  // 분할 후 남는 크기

    // 남는 공간이 최소 블록 크기(16B) 이상이면 분할
    if (remainder >= (2*DSIZE)) { 
        /* Case 1: 분할 (Splitting) */
        // 1. 요청한 블록을 할당
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // 2. 남는 블록을 가용 상태로 갱신
        bp = NEXT_BLKP(bp); // bp를 남는 블록으로 이동
        PUT(HDRP(bp), PACK(remainder, 0));
        PUT(FTRP(bp), PACK(remainder, 0));
    } 
    // 남는 공간이 16B 미만이면 (내부 단편화 감수)
    else { 
        /* Case 2: 분할 안 함 (통째로 사용) */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
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
    coalesce(bp);
}

static void* coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) { // 앞 뒤 할당
        return bp;
    }
    else if (prev_alloc && !next_alloc) { // 앞 할당 뒤 가용
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }
    else if (!prev_alloc && next_alloc) { // 앞 가용 뒤 할당
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    else { // 앞뒤 가용
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
    
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

    /* 2. 크기 조정 (오버헤드 및 정렬 요구사항 포함) */
    if (size <= DSIZE)
        asize = 2*DSIZE; // 최소 블록 크기 16바이트
    else
        // 8바이트 오버헤드 + 8바이트 배수로 올림
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* 3. 가용 리스트 검색 (find_fit) */
    if ((bp = find_fit(asize)) != NULL) {
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

    // 1. 새 크기로 malloc
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    // 2. 복사할 크기 계산
    old_block_size = GET_SIZE(HDRP(oldptr));
    // (old_block_size는 헤더/푸터 포함, size는 순수 페이로드)
    copySize = old_block_size - DSIZE; // 실제 페이로드 크기

    if (size < copySize) // 요청한 새 크기가 더 작으면
        copySize = size; // 새 크기만큼만 복사

    // 3. 데이터 복사 및 이전 블록 해제
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);

    return newptr;
}