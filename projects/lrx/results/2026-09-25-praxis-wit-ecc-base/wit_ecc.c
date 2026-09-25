// ecc(base) via rank-indexed full BFS from base=(1..m,0^r); prints ecc, reach,
// last 4 layer sizes. States = distinct permutations of multiset {0^r,1..m}.
// Derived from wit_rank.c (independent rank addressing). Usage: wit_ecc m r
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int n,m_,r_;
static uint64_t fact[25];
static uint64_t perms(int z,int k){ return fact[z+k]/fact[z]; }
static uint64_t rank_of(const char*w){
  int z=r_; uint32_t mask=0; for(int c=1;c<=m_;c++) mask|=1u<<c;
  uint64_t rk=0;
  for(int i=0;i<n;i++){
    int k=__builtin_popcount(mask);
    if(w[i]==0){ z--; }
    else{
      if(z>0) rk+=perms(z-1,k);
      uint32_t smaller=mask & ((1u<<w[i])-1);
      int cnt=__builtin_popcount(smaller);
      if(cnt) rk+=cnt*perms(z,k-1);
      mask&=~(1u<<w[i]);
    }
  }
  return rk;
}
typedef struct { uint32_t idx; char w[16]; } St;
static St *cur,*nxt; static size_t curn,ncurn,cap,ncap;
static uint8_t *dist;
static int grow(St**a,size_t*c,size_t need){ if(need<=*c)return 0; size_t nc=*c? *c*2:1024; while(nc<need)nc*=2; *a=realloc(*a,nc*sizeof(St)); if(!*a){fprintf(stderr,"OOM\n");exit(2);} *c=nc; return 0;}
static void push(const char*w,uint32_t idx){ grow(&nxt,&ncap,ncurn+1); St*s=&nxt[ncurn++]; s->idx=idx; memcpy(s->w,w,n); }
static inline void succ3(const char*w,char*a,char*b,char*c3){
  memcpy(a,w+1,n-1); a[n-1]=w[0];
  memcpy(b,w,n); {char t=b[0];b[0]=b[1];b[1]=t;}
  memcpy(c3+1,w,n-1); c3[0]=w[n-1];
}
int main(int argc,char**argv){
  m_=atoi(argv[1]); r_=atoi(argv[2]); n=m_+r_;
  for(int i=0;i<25;i++) fact[i]= i? fact[i-1]*i:1;
  uint64_t total=perms(r_,m_);
  fprintf(stderr,"n=%d m=%d r=%d states=%llu\n",n,m_,r_,(unsigned long long)total);
  dist=malloc(total); if(!dist){fprintf(stderr,"OOM dist\n");return 2;}
  memset(dist,255,total);
  char base[40]; memset(base,0,n); for(int c=1;c<=m_;c++) base[c-1]=(char)c;
  uint32_t bid=(uint32_t)rank_of(base);
  fprintf(stderr,"base rank=%u\n",bid);
  dist[bid]=0; push(base,bid);
  { St*t=cur;cur=nxt;nxt=t; size_t tc=cap;cap=ncap;ncap=tc; curn=ncurn; ncurn=0; }
  char buf[3][40];
  uint64_t reach=1; int ecc=0; size_t h[4]={0,0,0,0};
  for(int d=0;curn;d++){
    fprintf(stderr,"layer %d: %zu\n",d,curn);
    h[d&3]=curn;
    for(size_t i=0;i<curn;i++){
      const St*s=&cur[i];
      succ3(s->w,buf[0],buf[1],buf[2]);
      for(int k=0;k<3;k++){
        uint32_t idx=(uint32_t)rank_of(buf[k]);
        if(dist[idx]==255){dist[idx]=(uint8_t)(d+1); push(buf[k],idx); reach++;}
      }
    }
    ecc=d;
    { St*t2=cur;cur=nxt;nxt=t2; size_t tc2=cap;cap=ncap;ncap=tc2; curn=ncurn; ncurn=0; }
  }
  printf("VERDICT m=%d r=%d n=%d states=%llu reach=%llu ecc(base)=%d tail: %zu,%zu,%zu,%zu (layers %d..%d)\n",
    m_,r_,n,(unsigned long long)total,(unsigned long long)reach,ecc,
    h[(ecc-3)&3],h[(ecc-2)&3],h[(ecc-1)&3],h[ecc&3],ecc-3,ecc);
  return 0;
}
