/* Phase-resolved single-path Haar operator (Method B) and its finite cell majorant.
   Exact chain (PROVED MATH, see REPORT): along one P* path, theta_r = frac(2^{x_r} t_{b_r}) satisfies
       theta_{r+1} = frac(2^{g_r} (theta_r + D_r) / 9),  D_r uniform on {0..8}, independent of the past,
   g_r = i_r + k_r (two Geom(p) >= 1 odd steps), row r black iff ||2^{i_r} theta_r|| < 1/54, eligible iff k_r >= 2.
   Jensen-beta operator: (L f)(th) = sum_{i,k} p^2 q^{i+k-2} s^{[k>=2][black_i(th)]} (1/9) sum_D f(phi_{g,D}(th)),  s = 3^beta.
   Cell majorant on P = 54*2^Lc cells:  (Lt F)(I) = sum_g p^2 q^{g-2} ((g-1) + (s-1) cnt_g(I)) * (1/9) sum_D max_{J meets phi_{g,D}(I)} F(J)
   + tail_{g>G} * max F,  where cnt_g(I) = #{1<=i<=g-2 : I meets black_i} (i > Imax counted as meeting).
   If f <= F cellwise then L f <= Lt F cellwise, so E[val^beta] <= max(Lt^K 1) <= rho(Lt)^K / min(v)  (v Perron vector, max v = 1).
   Output: rho(Lt) by power iteration, and the implied c(beta) = beta*log3(2)/5 - log3 rho. */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
typedef __int128 i128;
int main(int argc,char**argv){
  int Lc=atoi(argv[1]); double beta=atof(argv[2]); double q=atof(argv[3]); int G=atoi(argv[4]); int iters=atoi(argv[5]);
  double p=1-q, s=pow(3.0,beta);
  double qlo = (argc>7)? atof(argv[7]) : q;
  double WG[512]; for(int g=2; g<512; g++){ double best=0; double cands[3]={qlo,q,(double)(g-2)/g}; for(int c=0;c<3;c++){ double x=cands[c]; if(x<qlo-1e-15||x>q+1e-15) continue; double w=(1-x)*(1-x)*pow(x,g-2); if(w>best) best=w; } WG[g]=best; }
  long P=54L<<Lc; int Imax=Lc+8;
  int LOG=1; while((1L<<LOG)<P) LOG++;
  /* black-meet table: meet[i][j] for i<=Imax */
  unsigned char *meet=calloc((Imax+1)*P,1);
  for(int i=1;i<=Imax;i++){
    for(long j=0;j<P;j++){
      /* cell [j/P,(j+1)/P); does 2^i*theta come within (open) 1/54 of an integer? exact in integers scaled by 54P */
      i128 lo=(i128)54*(((i128)1)<<i)*j, hi=(i128)54*(((i128)1)<<i)*(j+1); /* 54P * 2^i theta in [lo,hi) */
      i128 SP=(i128)54*P;
      int hit=0;
      if(hi-lo >= SP) hit=1; else {
        i128 n0=lo/SP; for(i128 n=n0-1;n<=n0+2 && !hit;n++){ i128 L=(54*n-1)*(i128)P, R=(54*n+1)*(i128)P; if(lo<R && hi>L) hit=1; }
      }
      meet[i*P+j]=hit;
    }
  }
  unsigned short *cnt=malloc(sizeof(unsigned short)*(G+1)*P);
  for(long j=0;j<P;j++){ int c=0; for(int g=0;g<=G;g++){ int i=g-2; if(i>=1){ c += (i<=Imax)? meet[i*P+j] : 1; } cnt[g*P+j]= (g>=3)? c:0; } }
  double *F=malloc(sizeof(double)*P), *Fn=malloc(sizeof(double)*P);
  double **sp=malloc(sizeof(double*)*(LOG+1)); for(int l=0;l<=LOG;l++) sp[l]=malloc(sizeof(double)*P);
  for(long j=0;j<P;j++) F[j]=1.0;
  double tailw=0, tailmass=0; for(int g=G+1; g<G+400 && g<512; g++){ tailw += WG[g]*((g-1)+(s-1)*(g-2)); tailmass+=WG[g]*(g-1);} 
  double rho=0;
  for(int it=0; it<iters; it++){
    /* sparse table for circular range max */
    for(long j=0;j<P;j++) sp[0][j]=F[j];
    for(int l=1;l<=LOG;l++){ long h=1L<<(l-1); for(long j=0;j<P;j++){ double a=sp[l-1][j], b=sp[l-1][(j+h)%P]; sp[l][j]=a>b?a:b; } }
    double maxF=0; for(long j=0;j<P;j++) if(F[j]>maxF) maxF=F[j];
    for(long j=0;j<P;j++) Fn[j]=tailw*maxF;
    for(int g=2; g<=G; g++){
      double wg=WG[g];
      if((((i128)1)<<g) >= (i128)9*P){ for(long j=0;j<P;j++) Fn[j]+= wg*((g-1)+(s-1)*cnt[g*P+j])*maxF; continue; }
      for(long j=0;j<P;j++){
        double R=0;
        for(int D=0; D<9; D++){
          /* image cell indices: [floor(2^g (j + D P)/9), floor(2^g (j+1+D P)/9)] inclusive (over-cover) */
          long a=((1L<<g)*(j+D*P))/9, b=((1L<<g)*(j+1+D*P))/9;
          double m;
          if(b-a+1 >= P) m=maxF; else {
            long len=(long)(b-a+1); long st=(long)(a%P); int l=0; while((2L<<l)<=len) l++;
            double x=sp[l][st], y=sp[l][(st+len-(1L<<l))%P]; m=x>y?x:y;
          }
          R+=m;
        }
        Fn[j]+= wg*((g-1)+(s-1)*cnt[g*P+j])*R/9.0;
      }
    }
    double mx=0; for(long j=0;j<P;j++) if(Fn[j]>mx) mx=Fn[j];
    rho=mx; for(long j=0;j<P;j++) F[j]=Fn[j]/mx;
  }
  double mn=1; for(long j=0;j<P;j++) if(F[j]<mn) mn=F[j];
  /* one more application to report max ratio Lt v / v (a certified-in-floating-point super-eigenvalue) */
  for(long j=0;j<P;j++) sp[0][j]=F[j];
  for(int l=1;l<=LOG;l++){ long h=1L<<(l-1); for(long j=0;j<P;j++){ double a=sp[l-1][j], b=sp[l-1][(j+h)%P]; sp[l][j]=a>b?a:b; } }
  double maxF=1; for(long j=0;j<P;j++) Fn[j]=tailw*maxF;
  for(int g=2; g<=G; g++){ double wg=WG[g]; if((((i128)1)<<g) >= (i128)9*P){ for(long j=0;j<P;j++) Fn[j]+= wg*((g-1)+(s-1)*cnt[g*P+j])*maxF; continue; } for(long j=0;j<P;j++){ double R=0; for(int D=0;D<9;D++){ long a=((1L<<g)*(j+D*P))/9, b=((1L<<g)*(j+1+D*P))/9; double m; if(b-a+1>=P) m=maxF; else { long len=(long)(b-a+1); long st=(long)(a%P); int l=0; while((2L<<l)<=len) l++; double x=sp[l][st], y=sp[l][(st+len-(1L<<l))%P]; m=x>y?x:y; } R+=m; } Fn[j]+=wg*((g-1)+(s-1)*cnt[g*P+j])*R/9.0; } }
  double ratio=0; for(long j=0;j<P;j++){ double r=Fn[j]/F[j]; if(r>ratio) ratio=r; }
  double c=beta*log(2)/5/log(3) - log(ratio)/log(3);
  if(argc>6){ FILE*fo=fopen(argv[6],"w"); for(long j=0;j<P;j++) fprintf(fo,"%.17g\n",F[j]); fclose(fo); }
  printf("Lc=%d P=%ld beta=%.3f q=%.6f G=%d  rho_iter=%.8f  maxratio(Lt v/v)=%.8f  min v=%.4e  tailmass=%.2e  c(beta)=%.5f\n",Lc,P,beta,q,G,rho,ratio,mn,tailmass,c);
  return 0;
}
