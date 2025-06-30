/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
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
    "ateam",
    /* First member's full name */
    "JongHo Lee",
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
/////////////////////<상수/매크로 정의>/////////////////////////////////////
#define WSIZE       4               
#define DSIZE       8             
#define CHUNKSIZE   (1 << 12)       /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// 하나의 헤더, 푸터  = 블록size  + 할당여부 (alloc) 
#define PACK(size, alloc) ((size) | (alloc))

// (*p) 의 값을 역참조해서 읽기(GET) / 쓰기 (WRITE)
#define GET(p)          (*(unsigned int *)(p))
#define PUT(p, val)     (*(unsigned int *)(p) = (val))

// Header/Footer에 저장된 정보에서 블록의 크기,할당 여부를
// 분리해서 읽어오는 데 사용
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

// 헤더와 푸터의 위치를 가리키는 포인터 
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음 블록의 시작주소 , 이전 블록의 시작주소 계산 매크로
// PREV_BLKP : 이전 블록의 푸터의 시작주소 가리킴
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
//#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))와 동일

#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
//////////////////////////////////////////////////////
static *heap_listp; // static : heap_listp 

//단편화 방지하기 위해 free 블록들끼리 병합
static void *coalesce(bp)
{
    //이전 블록에 접근할땐 footer 에 접근하는게 효율적
    //마지막 1비트만 가져와서 할당비트 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    // size : 현재 블록의 size
    size_t size = GET_SIZE(HDRP(bp));

    // Case 1 :  둘다 alloc
    if (prev_alloc & next_alloc){
        return bp;
    }

    // Case 2 :  이전블록-alloc 1, 다음블록-free 0
    // 현재 + 다음 병합
    else if (prev_alloc & !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); //다음 블록크기만큼 증가
        PUT(HDRP(bp),PACK(size,0)); //헤더 업데이트
        PUT(FTRP(bp),PACK(size,0)); //푸터 업데이트
    }

    // Case 3 :  이전블록- free 0 , 다음블록- alloc 1
    // 이전 + 현재 병합
    // 이전 블록의 header , 현재 블록의 footer만 수정
    else if (!prev_alloc & next_alloc){
        size += GET_SIZE(FTRP(PREV_BLKP(bp))); //이전 블록크기만큼 증가
        PUT(FTRP(bp),PACK(size,0)); //헤더 업데이트
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0)); //푸터 업데이트
        bp = PREV_BLKP(bp); //시작 포인터 이전블록으로 변경
    }

    // Case 4 :  이전블록- free 0 , 다음블록- free 0
    // 셋다 병합
    // 이전의 header, 다음의 footer만 수정
    else{
        size += GET_SIZE(FTRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));

        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp); //시작 포인터 변경
    }
    return bp;
}



// 새로운 free 블록을 힙 끝에 만들어주기 위해 사용
static void *extend_heap(size_t words)
{
    char * bp;
    size_t size;

    // 정렬을 유지하기 위해 짝수를 Allocate
    // 홀수면 1개의 WORD 를 더 할당
    size = (words % 2 ) ? (words * WSIZE) + WSIZE : words * WSIZE; 

    //mem_sbrk() 의 리턴이 -1 일때 (sbrk 의 반환형은 void* 이므로 형변환 필요)
    //조건이 참이든 거짓이든 먼저 bp = mem_sbrk(size) 무조건 실행
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size,0)); //헤더에 ( size | 0 ) 정보 쓰기
    PUT(FTRP(bp), PACK(size,0)); //푸터에 ( size | 0 ) 정보 쓰기
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1)); //다음 블록의 헤더 = 에필로그블록

    // 이전 블록이 FREE 라면 병합
    //프롤로그 블록 덕분에 맨 앞 블록이어도 동작
    return coalesce(bp);
}



//초기화 - mem_sbrk 등은 memlib.c에 정의
int mm_init(void)
{
    //예외처리 
    if ((heap_listp = mem_sbrk(4 * WSIZE)) ==(void *) -1 )
        return -1;

    PUT(heap_listp,0); // unused padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE,1)); // 프롤로그 header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE,1)); // 프롤로그 footer
    PUT(heap_listp + (3 * WSIZE), PACK(0,1)); //에필로그 header

    //힙 확장이 실패했을 때 예외처리
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

// 항상 블록의 크기를 alignment 배수의 크기로 할당하기 !
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

// 헤더와 푸터만 변경하고, 내용을 변경하지는 않음
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); //현재 블록의 사이즈

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    coalesce(bp); //병합
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