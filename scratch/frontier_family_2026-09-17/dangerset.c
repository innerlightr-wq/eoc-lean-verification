/* Exact phase-coordinate danger set of one idealized K-window (start state x0 = 0, no cap, s = 3, black eta = 1/54,
   geometric steps p = 1/log2(3)), with columns truncated at z <= Z.  T in [0,1): row r (r = 0..K-1) has phase
   t_r = frac(9^{K-1-r} T); cell (r, z) black iff ||2^z t_r|| < 1/54.  All breakpoints are multiples of
   1/Den, Den = 54 * 2^Z * 9^{K-1}, so danger is constant on each open cell (k/Den, (k+1)/Den); we evaluate at
   midpoints with exact integer arithmetic for the black tests.
   Output: danger bitmap statistics (measure, #arcs), Fourier |g(n)| for n <= NF, overlap mu(D ∩ 2^{-r} D)/mu(D)
   for r = 1..12 (dilation T -> 2^r T), and the distribution of window mass. */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
typedef unsigned __int128 u128;
int main(int argc, char **argv){
  int K = atoi(argv[1]), Z = atoi(argv[2]);
  double p = 1.0/log2(3.0), q = 1.0 - p, thr = pow(2.0, K/5.0);
  u128 Den = 54; for (int i=0;i<Z;i++) Den*=2; for (int i=0;i<K-1;i++) Den*=9;
  long D = (long)Den;
  unsigned char *bad = calloc(D, 1);
  double *G = malloc(sizeof(double)*(Z+4)), *Gn = malloc(sizeof(double)*(Z+4));
  long nbad = 0; double sumval = 0, maxval = 0;
  static unsigned char black[8][64];
  for (long k = 0; k < D; k++) {
    /* T = (2k+1)/(2 Den); t_r*2^z = frac(2^z 9^{K-1-r} (2k+1)/(2Den)); black iff dist < 1/54 */
    for (int r = 0; r < K; r++) {
      u128 mult = 1; for (int i=0;i<K-1-r;i++) mult*=9;
      u128 M2 = 2*Den;
      u128 num = ((u128)(2*k+1) * mult) % M2;       /* 9^f (2k+1) mod 2Den */
      for (int z = 0; z <= Z; z++) {
        /* x = num * 2^z / (2 Den) mod 1 ; dist < 1/54  <=>  54 * min(v, M2 - v) < M2, v = num*2^z mod M2 */
        u128 v = num;
        for (int i=0;i<z;i++) { v = (v*2) % M2; }
        u128 w = v < M2 - v ? v : M2 - v;
        black[r][z] = (54 * w < M2);
      }
    }
    for (int y=0;y<=Z+3;y++) G[y] = (y<=Z)?1.0:0.0;
    for (int r = K-1; r >= 0; r--) {
      int Pc[70]; int c=0; for (int z=0;z<=Z+3;z++){ if(z<=Z && black[r][z]) c++; Pc[z]=c; }
      double S0=0,S1=0,S2=0;
      for (int x=Z;x>=0;x--){ double g2=(x+2<=Z)?G[x+2]:0.0; double nS1=g2+q*(S1+S0), nS0=g2+q*S0, nS2=Pc[x]*g2+q*S2; S0=nS0;S1=nS1;S2=nS2; Gn[x]=p*p*(S1+2.0*S2-2.0*Pc[x]*S0); }
      for (int x=0;x<=Z;x++) G[x]=Gn[x]; for (int x=Z+1;x<=Z+3;x++) G[x]=0;
    }
    double val = G[0]; sumval += val; if (val > maxval) maxval = val;
    if (val > thr) { bad[k] = 1; nbad++; }
  }
  long arcs = 0; for (long k=0;k<D;k++) if (bad[k] && !bad[(k+D-1)%D]) arcs++;
  printf("K=%d Z=%d Den=%ld measure=%.6e arcs=%ld E[val]=%.6f max val=%.4f thr=%.4f\n", K, Z, D, (double)nbad/D, arcs, sumval/D, maxval, thr);
  /* Fourier on the bad list: top coefficients for n <= NF, with 2-adic and 3-adic valuations */
  int NF = atoi(argv[3]);
  long *lst = malloc(sizeof(long)*nbad); long c2=0; for (long k=0;k<D;k++) if (bad[k]) lst[c2++]=k;
  double mu = (double)nbad/D;
  double *mag = malloc(sizeof(double)*(NF+1)); double l1=0; double l1s=0;
  for (int n=1;n<=NF;n++){ double re=0,im=0; for(long i=0;i<nbad;i++){ double ang=-2*M_PI*n*(lst[i]+0.5)/D; re+=cos(ang); im+=sin(ang);} mag[n]=sqrt(re*re+im*im)/D/mu; l1+=mag[n];
    int nn=n, a=0,b=0; while(nn%2==0){nn/=2;a++;} while(nn%3==0){nn/=3;b++;} if (nn<=1) l1s+=mag[n]; }
  printf(" sum_{n<=%d}|g(n)|/mu = %.3f ; of which on n = 2^a 3^b: %.3f\n", NF, l1, l1s);
  printf(" top coefficients (n, |g|/mu, n/(2^a3^b)):");
  for (int t=0;t<16;t++){ int bi=1; for(int n=1;n<=NF;n++) if(mag[n]>mag[bi]) bi=n; int nn=bi; while(nn%2==0)nn/=2; while(nn%3==0)nn/=3; printf(" (%d,%.3f,%d)", bi, mag[bi], nn); mag[bi]=-1; }
  printf("\n");
  printf("dilation overlap mu(D ∩ 2^{-r}D)/mu(D)^2 for r=1..12:");
  for (int r = 1; r <= 12; r++) {
    /* T in cell k, 2^r T in cell floor(2^r(k+1/2)) mod D (cells are refined by 2^r; exact since D has factor 2^Z... approximate) */
    long cnt = 0;
    for (long k=0;k<D;k++) if (bad[k]) { long kk = (long)(((u128)(2*k+1) << r) / 2) % D; if (bad[kk]) cnt++; }
    printf(" %.2f", (double)cnt/D/(mu*mu));
  }
  printf("\n");
  return 0;
}
