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
// 명시적 = 42(util) + 40(thru) = 82/100
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
    "Jungle",
    /* First member's full name */
    "ShimWooJeong",
    /* First member's email address */
    "dnwjd040635@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

///////////프로그램 전반에 반복적으로 쓰이는 함수/변수들 매크로로 선언///////////
#define WSIZE 4             // 싱글 워드 사이즈
#define DSIZE 8             // 더블 워드 사이즈
#define CHUNKSIZE (1 << 12) // heap을 늘릴 때 필요한 사이즈 = 1을 왼쪽으로 12번 시프트 = 2의 12승 = 4096 = 4KB

// x와 y중 더 큰 값 반환하는 함수
#define MAX(x, y) ((x) > (y) ? (x) : (y))

// 블록 size와 할당 여부 비트를 통합해 헤더/풋터에 저장하게 될 값 반환
#define PACK(size, alloc) ((size) | (alloc))

// 주소 p의 위치에 워드를 읽고 쓰는 함수
#define GET(p) *((unsigned int *)(p)) // p가 가리키는 메모리 위치에 있는 값 읽음
// p를 unsigned int 포인터로 형변환 한 후(4바이트 단위로 읽어오기 위해)
// *연산자로 그 포인터가 가리키는 메모리 위치의 값을 역참조해 반환
#define PUT(p, val) *((unsigned int *)(p)) = val // p가 가리키는 메모리 위치에 val을 씀

#define GET_SIZE(p) (GET(p) & ~0x7) // p에 있는 헤더/풋터의 size 반환 0x7이 111인데 이걸로 비트마스킹 해서 블록 사이즈만큼만 읽어오도록
#define GET_ALLOC(p) (GET(p) & 0x1) // p에 있는 헤더/풋터의 할당비트 반환 0x1은 1인데 이걸로 비트마스킹 해서 할당 비트 읽어오도록

// bp = 블록 포인터
#define HDRP(bp) ((char *)(bp)-WSIZE)                        // 헤더가 가리키는 포인터 반환
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 풋터가 가리키는 포인터 반환

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // 다음 블록 포인터 반환
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   // 이전 블록 포인터 반환

// 명시적 할당기
#define GET_PRED(bp) (*(void **)(bp))
#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE))

// 명시적 할당기
static char *free_listp; // 첫 번째 가용 블록의 bp

// 묵시적 할당기 함수
static void *coalescing(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *extend_heap(size_t words);

// 명시적 할당기 추가 함수
static void remove_free_block(void *bp);
static void add_free_block(void *bp);
//////////////////////////////////////////////////////////////////

// mm_init(): 최초 가용 블록으로 힙 생성하는 함수
int mm_init(void)
{
    // 초기 빈 heap 생성
    // 묵시: 4워드, 명시: 8워드만큼 힙 top 늘림
    // heap_listp = mem_sbrk(4 * WSIZE);
    // free_listp = mem_sbrk(8 * WSIZE);

    if ((free_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)
    {
        return -1;
    }

    // padding, 한 워드만큼 생성
    PUT(free_listp, 0);                                // 패딩
    PUT(free_listp + (1 * WSIZE), PACK(4 * WSIZE, 1)); // 프롤로그 헤더
    PUT(free_listp + (2 * WSIZE), NULL);               // predecessor 포인터
    PUT(free_listp + (3 * WSIZE), NULL);               // successor 포인터
    PUT(free_listp + (4 * WSIZE), PACK(4 * WSIZE, 1)); // 프롤로그 풋터
    PUT(free_listp + (5 * WSIZE), PACK(0, 1));         // 에필로그 헤더

    // free_listp 가용 리스트 포인터의 첫 위치는 프롤로그 헤더 다음을 가리킴
    free_listp += DSIZE;

    /*포인터는 항상 header 뒤에 위치: 헤더를 읽어 다른 블록으로 가거나, 읽어오기 위해*/

    // extend_heap = heap 확장 한 번 해줌(묵시적과 달리 명시적은 DSIZE)
    if (extend_heap(CHUNKSIZE / DSIZE) == NULL)
    {
        return -1;
    }

    return 0;
}

// mm_malloc(): 가용 리스트에서 블록 할당하는 함수
void *mm_malloc(size_t size)
{
    size_t asize;       // 할당할 블록 사이즈
    size_t extend_size; // 확장할 블록 사이즈(find_fit에 실패할 경우 사용)
    void *bp;           // 할당된 블록 포인터

    // 요청 사이즈가 0일 때, NULL 반환
    if (size == 0)
    {
        return NULL;
    }

    // 요청된 사이즈 기준으로 실제 할당할 블록 크기 계산
    if (size <= DSIZE)
    {
        // 요청된 크기가 더블워드 사이즈보다 작은 경우
        // 최소 크기로 설정 = 2 * DSIZE
        // 헤더와 풋터를 포함해야 하니까 두 배로 줌
        asize = 2 * DSIZE;
    }
    else
    {
        // 요청된 크기가 더블워드 사이즈보다 큰 경우
        // 블록이 가질 수 있는 크기 중 최적화된 크기로 재조정
        // '요청한 size에 헤더와 풋터를 넣은 크기'가 가질 수 있는 8의 배수 중 최솟값
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    // 들어갈 수 있는 적절한 가용 블록 찾음
    if ((bp = find_fit(asize)) != NULL)
    {
        // 찾으면, 해당 블록에 메모리 할당 후 해당 블록의 포인터 반환
        place(bp, asize);
        return bp;
    }

    // 들어갈 수 있는 가용 블록이 없다 -> 추가적인 힙 요청/확장해 메모리 할당
    // 확장 블록 사이즈 = 조정할 블록 사이즈(asize)와 우리가 정의한 사이즈(CHUNKSIZE) 중에 큰 값
    extend_size = MAX(asize, CHUNKSIZE);
    bp = extend_heap(extend_size / WSIZE);

    if (bp == NULL)
    {
        // 힙 확장에 실패하면 NULL 반환
        return NULL;
    }
    // 이러면 힙이 확장됐으니, 새롭게 할당된 블록에 메모리 할당 후 블록 포인터 반환
    place(bp, asize);
    return bp;
}

// mm_free(): 블록 반환 후 경계 태그 연결로 인접 가용 블록과 통합하는 함수
void mm_free(void *bp)
{
    // 인자로 받은 bp를 확인해, 얼만큼 free할 지 사이즈를 받아옴
    size_t size = GET_SIZE(HDRP(bp));

    // 헤더와 풋터를 가용 상태로 만들어줌(할당여부 = 0으로)
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 이전&다음 확인하고 가용 블록 통합해주는 coalescing 함수 호출
    coalescing(bp);
}

void *mm_realloc(void *bp, size_t size)
{
    if (size <= 0)
    {
        mm_free(bp);
        return 0;
    }
    if (bp == NULL)
    {
        return mm_malloc(size);
    }
    void *newp = mm_malloc(size);

    if (newp == NULL)
    {
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(bp));
    if (size < oldsize)
    {
        oldsize = size;
    }
    memcpy(newp, bp, oldsize);
    mm_free(bp);
    return newp;
}

// coalescing(): 가용 블록끼리 연결(통합)하는 함수
static void *coalescing(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 가용 여부
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 블록 사이즈

    if (prev_alloc && next_alloc)
    {
        // Case 1: 이전&다음 블록 모두 할당 상태 = 현재 블록 할당에서 가용으로 변경
        // extend_heap에서 이 함수를 호출 할 땐, 어차피 이 조건에 안 들어옴
        // free에서 이 함수를 호출 할 땐, 이미 free에서 할당->가용 변경했으니 따로 free 안 함
        add_free_block(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc)
    {
        // Case 2: 이전 할당&다음 가용 상태 = 현재 블록은 다음 블록과 통합
        remove_free_block(NEXT_BLKP(bp));      // 다음 가용 블록을 가용 리스트에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더 확인, 그 블록 크기만큼 현재 블록 size에 더해줌
        PUT(HDRP(bp), PACK(size, 0));          // 헤더 갱신
        PUT(FTRP(bp), PACK(size, 0));          // 풋터 갱신
    }
    else if (!prev_alloc && next_alloc)
    {
        // Case 3: 이전 가용&다음 할당 상태 = 이전 블록은 현재 블록과 통합
        remove_free_block(PREV_BLKP(bp));        // 이전 가용 블록을 가용 리스트에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));   // 이전 블록의 헤더 확인, 그 블록 크기만큼 현재 블록 size에 더해줌
        PUT(FTRP(bp), PACK(size, 0));            // 풋터에 조정하려는 크기로 블록 size 변경
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 현재 헤더에서 이전 블록의 헤더 위치로 가, 블록 size 변경
        bp = PREV_BLKP(bp);                      // bp를 이전 블록의 헤더로 이동
    }
    else
    {
        // Case 4: 이전&다음 블록 모두 가용 상태 = 이전/현재/다음 모두 하나의 가용 블록으로 통합
        remove_free_block(PREV_BLKP(bp));                                      // 이전 가용 블록과
        remove_free_block(NEXT_BLKP(bp));                                      // 다음 가용 블록을 가용 리스트에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록 헤더~다음 블록 풋터까지로 size 늘림
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                               // 헤더부터 이전 블록 가서 size 수정
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));                               // 풋터는 다음 블록 가서 size 수정
        bp = PREV_BLKP(bp);                                                    // bp를 이전 블록의 헤더로 이동
    }
    // Coalescing에 의해 recently_fit이 빈 가용 블록에서 엉뚱한 위치를 가리킬 수 있기 때문에 bp로 업데이트 해줘야 함
    // 원래 잘 가리키고 있다가 가용 블록의 크기가 늘어날 수 있으니까 !

    add_free_block(bp); // 병합한 가용 블록을 가용 리스트에 추가
    return bp;          // Coalescing에 의해 적용된 bp 반환
                        // bp는 항상 블록의 헤더 뒤에 위치하도록 만들어줘야 함
}

// extend_heap(): 새 가용 블록으로 힙 확장하는 함수
static void *extend_heap(size_t words)
{
    char *bp;    // 블록 포인터
    size_t size; // unsigned int

    // 정렬 유지를 위해 짝수 개수의 워드를 할당
    // 홀수면 (words+1) * WSIZE, 짝수로 만들어서 할당
    // 짝수면 words * WSIZE
    size = (words % 2) ? (words + 1) * DSIZE : words * DSIZE;

    // sbrk를 사용해 size만큼 늘림 = 추가적인 힙 공간 요청
    // mem_sbrk(size) 실행 후, bp는 생성된 블록의 끝에 위치함
    // 또, old brk는 늘려지기 전 mem_brk 위치
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }

    // 가용 블록 헤더 생성
    // -> bp가 에필로그 블록 뒤에 있으니까 에필로그 블록 헤더를 참조해 size/0의 새로운 가용 블록 헤더로 초기화
    PUT(HDRP(bp), PACK(size, 0));
    // 가용 블록 풋터 생성
    PUT(FTRP(bp), PACK(size, 0));
    // 가용 블록 추가 -> 에필로그 헤더 위치 조정
    // 맨 끝에 에필로그 헤더 새롭게 할당
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalescing(bp);
}

// find_fit(): 가용 리스트에서 적절한 크기의 블록을 찾는 함수
static void *find_fit(size_t asize)
{
    // next_fit, best_fit은 mm_implicit에 있습니다

    // Emplicit Free List -> First_fit 검색
    void *bp;

    // for문으로 가용 리스트 탐색, 끝까지 가면 프롤로그 헤더는 할당 상태니까 for문 종료됨
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = GET_SUCC(bp))
    {
        if ((asize <= GET_SIZE(HDRP(bp))))
        {
            // asize보다 크거나 같아서 담을 수 있다면, 해당 bp 반환
            return bp;
        }
    }
    // 적절한 크기의 블록이 없었음 = null 반환
    return NULL;
}

// place(): 요청한 블록을 가용 블록에 배치,
// 나머지 부분의 크기가 최소 블록 크기거나 그보다 크다면 분할하는 함수
static void place(void *bp, size_t asize)
{
    // 현재 블록의 사이즈
    size_t csize = GET_SIZE(HDRP(bp));

    remove_free_block(bp); // 가용 리스트에서 해당 블록 제거
    // 현재 블록에 asize를 넣어도 최소 사이즈(2*DSIZE)만큼 남는다면
    if ((csize - asize) >= (2 * DSIZE))
    {
        // 헤더/풋터에 asize만큼 넣고 할당 여부 업데이트
        // 본래 헤더/풋터 사이즈에서 지금 넣는 사이즈(asize)로 갱신 = 분할하는 효과
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // 블록 포인터 위치 갱신
        bp = NEXT_BLKP(bp);
        // asize를 넣고 남은 블록은 다 가용 여부로 업데이트
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));

        add_free_block(bp); // 남은 블록 가용 리스트에 추가
    }
    else
    {
        // 현재 블록이 asize랑 딱 맞으면 헤더/풋터만 할당 여부로 업데이트
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

// 가용 리스트 블록 제거 함수
static void remove_free_block(void *bp)
{
    // bp가 free_listp를 가리키고 있을 때 = 첫 번째 블록.. 프롤로그 블록이니까 안 지움
    if (bp == free_listp)
    {
        GET_PRED(GET_SUCC(bp)) = NULL;
        free_listp = GET_SUCC(bp);
    }
    else
    {
        GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
    }
}

// 가용 리스트 블록 추가 함수 (맨 앞에 추가함)
static void add_free_block(void *bp)
{
    GET_SUCC(bp) = free_listp;     // bp의 SUCC은 루트가 가리키던 블록
    if (free_listp != NULL)        // free list에 블록이 존재했을 경우만
        GET_PRED(free_listp) = bp; // 루트였던 블록의 PRED를 추가된 블록으로 연결
    free_listp = bp;               // 루트를 현재 블록으로 변경
}