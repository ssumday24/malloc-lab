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
    " Krafton Jungle",
    /* First member's full name */
    " JongHo Lee",
    /* First member's email address */
    "zx546800@naver.com",
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
static char *heap_listp; // static 전역변수 : heap_listp 

static void *find_fit(size_t asize);
static void place(void* bp, size_t asize);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);

//#define Next_fit // Next_fit 선언 -> First,Best 진행시 주석처리
static char *rover;  // Next_fit을 위한 전역 포인터변수

#define Best_fit  //Best_fit 선언

//초기화 - mem_sbrk 등은 memlib.c에 정의
int mm_init(void)
{
    //예외처리 
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp,0); // unused padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE,1)); // 프롤로그 header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE,1)); // 프롤로그 footer
    PUT(heap_listp + (3 * WSIZE), PACK(0,1)); //에필로그 header
    
    // 논리흐름상, heap_list 는 프롤로그 footer 부터 시작
    heap_listp += (2*WSIZE);
    rover = heap_listp;

    //힙 확장이 실패했을 때 예외처리
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
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

// 헤더와 푸터만 변경하고, 내용을 변경하지는 않음
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); //현재 블록의 사이즈

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));

    #ifdef Next_fit
    // 만약 rover가 지금 free하는 블록을 가리키고 있으면, rover를 heap_listp로 리셋
    if (rover == bp)
        rover = heap_listp;
    #endif

    coalesce(bp); //병합
}

//단편화 방지하기 위해 free 블록들끼리 병합
static void *coalesce(void *bp)
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
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); //이전 블록크기만큼 증가
        PUT(FTRP(bp),PACK(size,0)); //푸터 alloc : 0 업데이트
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0)); //헤더 업데이트
        bp = PREV_BLKP(bp); //시작 포인터 이전블록으로 변경
    }

    // Case 4 :  이전블록- free 0 , 다음블록- free 0
    // 셋다 병합
    // 이전의 header, 다음의 footer만 수정
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));

        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0)); //이전블록 헤더
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0)); //다음블록 푸터
        bp = PREV_BLKP(bp); //시작 포인터 변경
    }
    return bp;
}

// 항상 블록의 크기를 alignment 배수 (여기선 8) 의 크기로 할당하기 !
void *mm_malloc(size_t size)
{
    size_t asize; // 조정 된 블록사이즈 : (payload + header/footer 포함)
    size_t extendsize; // heap 을 확장할 크기
    char* bp;

    if (size ==0)
        return NULL; //예외처리

    if (size <=DSIZE) //최소 블록 크기(8배수)보장 (header+footer+최소payload)
        asize = 2 * DSIZE;
    
    else
        //DSIZE 초과면 8의 배수로 올림       
        asize = DSIZE * ( ( size + (DSIZE) + (DSIZE - 1) ) / DSIZE);
    
    // 가용 리스트에서 asize를 만족하는 free 블록 찾기
    // 찾았으면 place() 로 블록 할당
    // find_fit 은 First_fit, Next_fit , Best_fit 등
    if ((bp = find_fit(asize)) != NULL){
        place(bp,asize);
        return bp;
    }

    // 찾지 못했을때 :  heap 확장
    extendsize = MAX(asize,CHUNKSIZE);

    // 한번에 `최소` CHUNK SIZE 이상 확장 - extend는 무조건 실행됨
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL )
        return NULL;
    
    //확장한 블록에 배정
    place(bp,asize);
    return bp;
    
}   

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    // 입력받은 size 만큼 메모리 할당
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    // 기존 oldptr 블록의 크기 읽어옴
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);

    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

//가용 리스트에서 Fist_fit or Next_fit검색 수행
//First_fit: 리스트를 처음부터 검색해서, '크기가 맞는 첫번째 Free블록' 선택
//Next_fit : 이전 검색이 종료된 지점에서 검색 시작
//Best_fit : 리스트 전체 탐색후 `크기가 맞는` `가장 작은 블록` 선택
static void *find_fit(size_t asize)
{
    // asize를 만족하는 free 블록 찾기
    // heap_listp 는 프롤로그의 footer 부터 시작
    
    #ifdef Best_fit
    char * bp = heap_listp; 
    char * best_select = NULL; //선택할 블록
    size_t min=__SIZE_MAX__; //최소 블록 크기 min

    //프롤로그 ~ 에필로그 블록까지 탐색
    while (GET_SIZE(HDRP(bp))!=0)
    {    
        // free 블록이면서, 크기가 asize 이상이면서,
        // 가장 작은 블록 업데이트
        if (!GET_ALLOC(HDRP(bp)) &&
            asize <= GET_SIZE(HDRP(bp)))
        {
            if (GET_SIZE(HDRP(bp)) < min )
            {min = GET_SIZE(HDRP(bp));
            best_select = bp; // 그 최소블록 포인터를 저장
            
            if (min == asize) // 딱 맞는 블록이면 바로 반환
                return best_select;
            }
        }    

        bp = NEXT_BLKP(bp);  //못찾았으면 다음블록 이동
    }

    return best_select; // 최소블록 주소 반환



    #elif defined (Next_fit) 
    char *start = rover; //start에 값이 바뀌기전 rover 저장

    // 1. rover ~ 에필로그까지 탐색
    while(GET_SIZE(HDRP(rover)) != 0) {
        if(GET_ALLOC(HDRP(rover)) == 0 && asize <= GET_SIZE(HDRP(rover)))
            return rover;
        else
            rover = NEXT_BLKP(rover);
    }

    // 2. heap_listp ~ start 이전까지 탐색
    rover = heap_listp;
    while (rover < start) {
        if(GET_ALLOC(HDRP(rover)) == 0 && asize <= GET_SIZE(HDRP(rover)))
            return rover;
        else
            rover = NEXT_BLKP(rover);
    }

    #else //First_fit : Next,Best 둘다 주석처리 
    /*
    GET_SIZE(HDRP(bp)) 로 접근후, 다음블록으로이동
    bp = next_blkp(bp)  
    종료조건 : 에필로그 블록 (size=0, alloc=0)
    */
    char *bp = heap_listp;

    while (GET_SIZE(HDRP(bp)) != 0 )
    {
        // 블록의 크기가 충분하고 , Alloc비트 == 0 이라면
        if ( asize <= GET_SIZE(HDRP(bp)) &&
              !GET_ALLOC(HDRP(bp))
            )
            return bp;
        else
            bp = NEXT_BLKP(bp); //다음블록 이동
    }

    #endif

    //에러 검출부분
    fprintf(stderr, "[find_fit] No fit found for size: %zu bytes\n", asize);
    
    return NULL; //못찾았으면 NULL 반환
}

// 확장한 블록에 배정
static void place(void* bp, size_t asize)
{
    size_t cur_size = GET_SIZE(HDRP(bp)); //현재블록 크기

    // 분할이 가능한지 확인 (최소 블록 크기 이상 남을때)
    // asize 와 (cur_size - asize) 로 분할
    if ((cur_size - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp),PACK(asize,1)); //헤더에 할당표시
        PUT(FTRP(bp),PACK(asize,1)); //푸터에 할당표시

        // 나머지 부분을 free 블록으로 만들기
        char *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp),PACK(cur_size - asize, 0)); // free 헤더
        PUT(FTRP(next_bp),PACK(cur_size - asize, 0)); // free 푸터

    }

    else //분할X ,전체블록 Cur_size 할당 
    { 
        PUT(HDRP(bp),PACK(cur_size,1)); //헤더에 할당표시
        PUT(FTRP(bp),PACK(cur_size,1)); //푸터에 할당표시
    }


}