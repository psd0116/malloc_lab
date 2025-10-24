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
#define GET_ALLOC(p) ((GET(p) &~0x1)) // 최하위 1비트만 읽기

#define HDRP(bp) ((char *)(bp) - WSIZE) // bp에서 4바이트 앞으로 (헤더 주소 읽기)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // bp + 블록크기 - 8B (푸터 주소 읽기)

#define NEXT_BLKP(bp) ((char *) + GET_SIZE(((char *)(bp) - WSIZE))) // bp를 이용해 다음 블록의 페이로드 주소를 계산
#define PREV_BLKP(bp) ((char *) - GET_SIZE(((char *)(bp) - DSIZE))) // bp를 이용해 이전 블록의 페이로드 주소를 계산

static char* heap_listp;

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


int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE) == (void *) -1)){
        return -1;
    }
    PUT(heap_listp, 0); // 주소 0에 4바이트 패딩을 두어서, 모든 페이로드가 8 바이트경계에 정렬되도록 한다.
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE,1)); // 프롤로그 블록 지정
    PUT(heap_listp + (2 * WSIZE), PUT(DSIZE,1)); // 에필로그 블록 지정
    PUT(heap_listp + (3 * WSIZE), PUT(0,1));
    heap_listp += (2 * WSIZE);

        if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
            return -1;
        }

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
        return NULL;
    else
    {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}