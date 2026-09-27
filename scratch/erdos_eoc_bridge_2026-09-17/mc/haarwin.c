/* Haar-model K-window mass for the EOC geometric odd-dark kernel (idealized: no cap, p = 1/log2(3)).
   Phase: v_b = xi mod 3^b built from uniform random ternary digits (exact 256-bit integers); row r uses depth
   b = b0 + 2r and tests column z (relative to window start x0 = 0) by the exact integer test
   black_eta(z,r):  eta_den * |centered(2^z v_b mod 3^b)| < 3^b.
   Mass val = sum_y ker(0,y) with block weight p^2 q^{y-x-2} * sum_{z in (x,y)} (s if z <= y-2 and black else 1),
   s = 3 (exactly the Lean geoW/oddW kernel with the dark predicate replaced by black_eta, no cap).
   Output (stdout, text): for each K in list: n, #(val > 2^{K/5}), sums of val^beta, histogram of log2(val)/K. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
typedef unsigned __int128 u128;
typedef struct { u128 lo, hi; } u256;
static inline int cmp(u256 a, u256 b){ if(a.hi!=b.hi) return a.hi<b.hi?-1:1; if(a.lo!=b.lo) return a.lo<b.lo?-1:1; return 0; }
static inline u256 add(u256 a, u256 b){ u256 r; r.lo=a.lo+b.lo; r.hi=a.hi+b.hi+(r.lo<a.lo); return r; }
static inline u256 sub(u256 a, u256 b){ u256 r; r.lo=a.lo-b.lo; r.hi=a.hi-b.hi-(a.lo<b.lo); return r; }
static inline u256 shl1(u256 a){ u256 r; r.hi=(a.hi<<1)|(a.lo>>127); r.lo=a.lo<<1; return r; }
static inline u256 shr1(u256 a){ u256 r; r.lo=(a.lo>>1)|(a.hi<<127); r.hi=a.hi>>1; return r; }
static inline u256 mulsmall(u256 a, unsigned m){ u256 r={0,0}; for(unsigned i=0;i<m;i++) r=add(r,a); return r; }
static unsigned long long s[2];
static inline unsigned long long rng(void){ unsigned long long s1=s[0]; const unsigned long long s0=s[1]; s[0]=s0; s1^=s1<<23; s[1]=s1^s0^(s1>>17)^(s0>>26); return s[1]+s0; }
static inline unsigned rand3(void){ return (unsigned)(((u128)rng()*3)>>64); }
#define MAXB 160
#define MAXZ 200
#define MAXK 40
int main(int argc, char **argv){
  int Kmax=atoi(argv[1]); long nsamp=atol(argv[2]); int etaden=atoi(argv[3]); unsigned long long seed=strtoull(argv[4],0,10);
  int nK=argc-5; int Ks[32]; for(int i=0;i<nK;i++) Ks[i]=atoi(argv[5+i]);
  s[0]=seed*0x9E3779B97F4A7C15ULL+1; s[1]=seed^0xD1B54A32D192ED03ULL; for(int i=0;i<20;i++) rng();
  double alpha=log2(3.0), p=1.0/alpha, q=1.0-p;
  int Zmax=(int)ceil(2.0*Kmax/p)+40; if(Zmax>=MAXZ-3){fprintf(stderr,"Z too big\n");return 1;}
  int b0=(int)ceil((Zmax+30)*log(2)/log(3))+4; int B=b0+2*Kmax; if(B>=MAXB||B*log2(3.0)>250){fprintf(stderr,"B too big %d\n",B);return 1;}
  u256 pw[MAXB+1]; pw[0].lo=1; pw[0].hi=0; for(int i=1;i<=MAXB;i++) pw[i]=mulsmall(pw[i-1],3);
  static unsigned char black[MAXK][MAXZ];
  static double G[MAXZ+4], Gn[MAXZ+4];
  double betas[]={0.5,1,1.5,2,2.5,3,4,5,6,8}; int nb=10;
  static double mom[32][10]; static long danger[32]; static long hist[32][400];
  memset(mom,0,sizeof mom); memset(danger,0,sizeof danger); memset(hist,0,sizeof hist);
  for(long it=0; it<nsamp; it++){
    u256 v={0,0};
    for(int i=0;i<b0;i++){ unsigned d=rand3(); if(d) v=add(v, d==1?pw[i]:shl1(pw[i])); }
    for(int r=0;r<Kmax;r++){
      int b=b0+2*r;
      if(r>0){ int bp=b-2; for(int i=bp;i<b;i++){ unsigned d=rand3(); if(d) v=add(v, d==1?pw[i]:shl1(pw[i])); } }
      u256 m=pw[b], half=shr1(pw[b]), thr=pw[b-3]; u256 w=v;
      for(int z=0; z<=Zmax; z++){
        u256 a = (cmp(w,half)>0)? sub(m,w) : w;
        u256 t = (etaden==54)? shl1(a) : shl1(shl1(a));   /* 2|y| or 4|y| */
        black[r][z] = cmp(t,thr)<0;
        w=shl1(w); if(cmp(w,m)>=0) w=sub(w,m);
      }
    }
    for(int ki=0; ki<nK; ki++){
      int K=Ks[ki];
      for(int y=0;y<=Zmax+3;y++) G[y]= (y<=Zmax)?1.0:0.0;
      for(int r=K-1;r>=0;r--){
        int Pc[MAXZ+4]; int c=0; for(int z=0;z<=Zmax+3;z++){ if(z<=Zmax && black[r][z]) c++; Pc[z]=c; }
        double S0=0,S1=0,S2=0;
        for(int x=Zmax;x>=0;x--){
          double g2 = (x+2<=Zmax)? G[x+2]:0.0;
          double nS1 = g2 + q*(S1+S0);
          double nS0 = g2 + q*S0;
          double nS2 = Pc[x]*g2 + q*S2;
          S0=nS0; S1=nS1; S2=nS2;
          Gn[x] = p*p*(S1 + 2.0*S2 - 2.0*Pc[x]*S0);
        }
        for(int x=0;x<=Zmax;x++) G[x]=Gn[x];
        for(int x=Zmax+1;x<=Zmax+3;x++) G[x]=0;
      }
      double val=G[0];
      if(val > pow(2.0, K/5.0)) danger[ki]++;
      for(int j=0;j<nb;j++) mom[ki][j]+=pow(val,betas[j]);
      double l=log2(val)/K; int bin=(int)floor((l+1.0)/0.005); if(bin<0)bin=0; if(bin>399)bin=399; hist[ki][bin]++;
    }
  }
  printf("# Kmax=%d n=%ld eta=1/%d Zmax=%d b0=%d\n",Kmax,nsamp,etaden,Zmax,b0);
  for(int ki=0;ki<nK;ki++){
    printf("K %d n %ld danger %ld mom",Ks[ki],nsamp,danger[ki]);
    for(int j=0;j<nb;j++) printf(" %.10e",mom[ki][j]);
    printf(" hist"); for(int b=0;b<400;b++) printf(" %ld",hist[ki][b]); printf("\n");
  }
  return 0;
}
