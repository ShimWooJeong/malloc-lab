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
    "Jungle",
    /* First member's full name */
    "ShimWooJeong",
    /* First member's email address */
    "dnwjd040635@gmail.com",
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

///////////프로그램 전반에 반복적으로 쓰이는 함수/변수들 매크로로 선언///////////
#define WSIZE 4 //싱글 워드 사이즈
#define DSIZE 8 //더블 워드 사이즈
#define CHUNKSIZE (1<<12) //heap을 늘릴 때 필요한 사이즈 = 1을 왼쪽으로 12번 시프트 = 2의 12승 = 4096 = 4KB

//x와 y중 더 큰 값 반환하는 함수
#define MAX(x, y) ((x) > (y) ? (x) : (y)) 

//블록 size와 할당 여부 비트를 통합해 헤더/풋터에 저장하게 될 값 반환
#define PACK(size, alloc) ((size) | (alloc))

//주소 p의 위치에 워드를 읽고 쓰는 함수
#define GET(p) *((unsigned int *)(p)) //p가 가리키는 메모리 위치에 있는 값 읽음
//p를 unsigned int 포인터로 형변환 한 후(4바이트 단위로 읽어오기 위해)
//* 연산자로 그 포인터가 가리키는 메모리 위치의 값을 역참조해 반환
#define PUT(p, val) *((unsigned int *)(p)) = val //p가 가리키는 메모리 위치에 val을 씀

#define GET_SIZE(p) (GET(p) & ~0x7) //p에 있는 헤더/풋터의 size 반환
#define GET_ALLOC(p) (GET(p) & 0x1) //p에 있는 헤더/풋터의 할당비트 반환

//bp = 블록 포인터
#define HDRP(bp) ((char *)(bp) - WSIZE) //헤더가 가리키는 포인터 반환
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //풋터가 가리키는 포인터 반환

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //다음 블록 포인터 반환
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //이전 블록 포인터 반환

static char *heap_listp; //처음에 쓸 가용블록 힙 생성 = 힙의 시작지점이 됨
//////////////////////////////////////////////////////////////////

//coalescing(): 가용 블록끼리 연결(통합)하는 함수
static void *coalescing(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //이전 블록 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //다음 블록 가용 여부
    size_t size = GET_SIZE(HDRP(bp)); //현재 블록 사이즈
    
    if(prev_alloc && next_alloc){
        //Case 1: 이전&다음 블록 모두 할당 상태 = 현재 블록 할당에서 가용으로 변경
        //extend_heap에서 이 함수를 호출 할 땐, 어차피 이 조건에 안 들어옴
        //free에서 이 함수를 호출 할 땐, 이미 free에서 할당->가용 변경했으니 따로 free 안 함
        return bp;
    }
    else if(prev_alloc && !next_alloc){
        //Case 2: 이전 할당&다음 가용 상태 = 현재 블록은 다음 블록과 통합
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); //다음 블록의 헤더 확인, 그 블록 크기만큼 현재 블록 size에 더해줌
        PUT(HDRP(bp), PACK(size, 0)); //헤더 갱신
        PUT(FTRP(bp), PACK(size, 0)); //풋터 갱신
    }
    else if(!prev_alloc && next_alloc){
        //Case 3: 이전 가용&다음 할당 상태 = 이전 블록은 현재 블록과 통합
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); //이전 블록의 헤더 확인, 그 블록 크기만큼 현재 블록 size에 더해줌
        PUT(FTRP(bp), PACK(size, 0)); //풋터에 조정하려는 크기로 블록 size 변경
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); //현재 헤더에서 이전 블록의 헤더 위치로 가, 블록 size 변경
        bp = PREV_BLKP(bp); //bp를 이전 블록의 헤더로 이동
    }
    else{
        //Case 4: 이전&다음 블록 모두 가용 상태 = 이전/현재/다음 모두 하나의 가용 블록으로 통합
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); //이전 블록 헤더~다음 블록 풋터까지로 size 늘림
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); //헤더부터 이전 블록 가서 size 수정
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); //풋터는 다음 블록 가서 size 수정
        bp = PREV_BLKP(bp); //bp를 이전 블록의 헤더로 이동
    }
    return bp; //Coalescing에 의해 적용된 bp 반환
               //bp는 항상 블록의 헤더 뒤에 위치하도록 만들어줘야 함
}

//extend_heap(): 새 가용 블록으로 힙 확장하는 함수
static void *extend_heap(size_t words){
    char *bp; //블록 포인터
    size_t size; //unsigned int

    //정렬 유지를 위해 짝수 개수의 워드를 할당
    //홀수면 (words+1) * WSIZE, 짝수로 만들어서 할당
    //짝수면 words * WSIZE
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    //sbrk를 사용해 size만큼 늘림 = 추가적인 힙 공간 요청
    //mem_sbrk(size) 실행 후, bp는 생성된 블록의 끝에 위치함
    //또, old brk는 늘려지기 전 mem_brk 위치
    if((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }

    //가용 블록 헤더 생성
    PUT(HDRP(bp), PACK(size, 0));
    //가용 블록 풋터 생성
    PUT(FTRP(bp), PACK(size, 0));
    //가용 블록 추가 -> 에필로그 헤더 위치 조정
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalescing(bp);
}

//mm_init(): 최초 가용 블록으로 힙 생성하는 함수
int mm_init(void)
{
    //초기 빈 heap 생성
    //4워드만큼 힙 top 늘림
    //heap_listp = mem_sbrk(4*WSIZE);

    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){
        return -1;
    }

    //padding, 한 워드만큼 생성
    PUT(heap_listp, 0);
    //heap_listp보다 1워드/2워드 간 위치에 프롤로그 헤더/풋터 생성
    //PACK = 블록 사이즈(DSIZE)+할당여부(1)
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    //그 뒤에, 에필로그 블록 헤더 생성 = 점점 뒤로 밀림
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    //프롤로그 헤더/풋터 사이로 heap_list 포인터를 옮김
    heap_listp += (2 * WSIZE);

    /*포인터는 항상 header 뒤에 위치: 헤더를 읽어 다른 블록으로 가거나, 읽어오기 위해*/

    //extend_heap = heap 확장 한 번 해줌
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }

    return 0;
}

//find_fit(): 가용 리스트에서 적절한 크기의 블록을 찾는 함수
static void *find_fit(size_t asize){
    // Best_fit 검색 = 58점
    void *bp;
    void *best_fit = NULL; //best_fit bp
    size_t min_size = __INT_MAX__; //넣으려는 사이즈와 가용 블록의 차이의 최솟값

    //for문으로 가용 리스트 탐색, 끝까지 가면 에필로그 헤더는 0이니까 for문 종료됨
    for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        //이 블록이 가용상태고 &&  asize보다 크거나 같아서 담을 수 있다면
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            //넣으려는 사이즈와 가용 블록의 사이즈가 일치하면 바로 해당 블록 포인터 반환
            if(asize == GET_SIZE(HDRP(bp))){
                return bp;
            }else{
                //다른 가용 블록 중 가장 적은 차이가 나는 블록으로 골라내기
                if(GET_SIZE(HDRP(bp)) < min_size){
                    min_size = GET_SIZE(HDRP(bp));
                    best_fit = bp;
                }
            }
        }
    }
    
    return best_fit;
    
    // // First_fit 검색 = 52점
    // void *bp;
    
    // //for문으로 가용 리스트 탐색, 끝까지 가면 에필로그 헤더는 0이니까 for문 종료됨
    // for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
    //     if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
    //         //이 블록이 가용상태고 &&  asize보다 크거나 같아서 담을 수 있다면, 해당 bp 반환
    //         return bp;
    //     }
    // }
    // //적절한 크기의 블록이 없었음 = null 반환
    // return NULL;
}

//place(): 요청한 블록을 가용 블록의 시작 부분에 배치,
//나머지 부분의 크기가 최소 블록 크기거나 그보다 크다면 분할하는 함수
static void place(void *bp, size_t asize){
    //현재 블록의 사이즈
    size_t csize = GET_SIZE(HDRP(bp));

    //현재 블록에 asize를 넣어도 최소 사이즈(2*DSIZE)만큼 남는다면
    if((csize - asize) >= (2 * DSIZE)){
        //헤더/풋터에 asize만큼 넣고 할당 여부 업데이트
        //본래 헤더/풋터 사이즈에서 지금 넣는 사이즈(asize)로 갱신 = 분할하는 효과
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        //블록 포인터 위치 갱신
        bp = NEXT_BLKP(bp);
        //asize를 넣고 남은 블록은 다 가용 여부로 업데이트
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else{
        //현재 블록이 asize랑 딱 맞으면 헤더/풋터만 할당 여부로 업데이트
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

//mm_malloc(): 가용 리스트에서 블록 할당하는 함수
void *mm_malloc(size_t size)
{
    size_t asize; //할당할 블록 사이즈
    size_t extend_size; //확장할 블록 사이즈(find_fit에 실패할 경우 사용)
    char *bp; //할당된 블록 포인터

    //요청 사이즈가 0일 때, NULL 반환
    if(size == 0){
        return NULL;
    }

    //요청된 사이즈 기준으로 실제 할당할 블록 크기 계산 
    if(size <= DSIZE){
        //요청된 크기가 더블워드 사이즈보다 작은 경우
        //최소 크기로 설정 = 2 * DSIZE
        //헤더와 풋터를 포함해야 하니까 두 배로 줌
        asize = 2 * DSIZE;
    }
    else{
        //요청된 크기가 더블워드 사이즈보다 큰 경우
        //블록이 가질 수 있는 크기 중 최적화된 크기로 재조정
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    //들어갈 수 있는 적절한 가용 블록 찾음
    if((bp = find_fit(asize)) != NULL){
        //찾으면, 해당 블록에 메모리 할당 후 해당 블록의 포인터 반환
        place(bp, asize);
        return bp;
    }

    //들어갈 수 있는 가용 블록이 없다 -> 추가적인 힙 요청/확장해 메모리 할당
    //확장 블록 사이즈 = 조정할 블록 사이즈(asize)와 우리가 정의한 사이즈(CHUNKSIZE) 중에 큰 값
    extend_size = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extend_size/WSIZE)) == NULL){
        //힙 확장에 실패하면 NULL 반환
        return NULL;
    }
    //이러면 힙이 확장됐으니, 새롭게 할당된 블록에 메모리 할당 후 블록 포인터 반환
    place(bp, asize);
    return bp;
}

//mm_free(): 블록 반환 후 경계 태그 연결로 인접 가용 블록과 통합하는 함수
void mm_free(void *bp)
{
    //인자로 받은 bp를 확인해, 얼만큼 free할 지 사이즈를 받아옴
    size_t size = GET_SIZE(HDRP(bp));

    //헤더와 풋터를 가용 상태로 만들어줌(할당여부 = 0으로)
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    
    //이전&다음 확인하고 가용 블록 통합해주는 coalescing 함수 호출
    coalescing(bp);
}

void *mm_realloc(void *bp, size_t size)
{
    if(size <= 0){
        mm_free(bp);
        return 0;
    }
    if(bp == NULL){
        return mm_malloc(size);
    }
    void *newp = mm_malloc(size);

    if(newp == NULL){
        return 0;
    }                        
    size_t oldsize = GET_SIZE(HDRP(bp));
    if(size < oldsize){
        oldsize = size;
    }
    memcpy(newp, bp, oldsize);
    mm_free(bp);
    return newp;
}














