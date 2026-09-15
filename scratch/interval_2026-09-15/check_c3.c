// Exact check of the 3-adic interval-sieve bound (C3, Minkowski form) at small j0:
//   a_u(exact) = sum_{lambda in cshell u} |Phi(lambda)|^2 / (#cshell * |P|^2)   vs   bound (1-2^-t)^-1 (sum_S g_S min(p_S, sqrt(kappa p_S))/|P|)^2.
// usage: check_c3 J sigma t umax
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static const double AL = 1.5849625007211562;
static int J, sg, t, m, bb[64], S[64];
static double f[64][128], g[64][128];
static uint64_t inv3p[64], MASK;
static uint64_t *Z; static int *path_S; static long np, cap;
static void dfs(int i, int s, uint64_t z) {  // S[i] = s, z = sum_{l<i} inv3^(l+1) 2^{S_l}
  if (i == J) { if (s != sg) return; if (np == cap) { cap = cap ? 2 * cap : 1024; Z = realloc(Z, cap * 8); path_S = realloc(path_S, cap * 64 * sizeof(int)); }
    Z[np] = z & MASK; for (int l = 0; l <= J; l++) path_S[np * 64 + l] = S[l]; np++; return; }
  uint64_t z2 = (z + inv3p[i] * (((uint64_t)1) << s)) & MASK;
  for (int s2 = s + 1; s2 <= bb[i + 1] && s2 <= sg; s2++) { if (g[i + 1][s2] == 0) continue; S[i + 1] = s2; dfs(i + 1, s2, z2); }
}
int main(int argc, char **argv) {
  J = atoi(argv[1]); sg = atoi(argv[2]); t = atoi(argv[3]); int umax = atoi(argv[4]); m = sg + t + 1; MASK = (m >= 64) ? ~0ULL : ((1ULL << m) - 1);
  for (int j = 0; j < 64; j++) bb[j] = (int)floor(j * AL);
  f[0][0] = 1; for (int i = 0; i < J; i++) for (int s = 0; s <= bb[i]; s++) if (f[i][s] > 0) for (int s2 = s + 1; s2 <= bb[i + 1]; s2++) f[i + 1][s2] += f[i][s];
  g[J][sg] = 1; for (int i = J - 1; i >= 0; i--) for (int s = 0; s <= bb[i]; s++) for (int s2 = s + 1; s2 <= bb[i + 1] && s2 <= sg; s2++) g[i][s] += g[i + 1][s2];
  // inverse of 3^(l+1) mod 2^64 (then masked)
  uint64_t inv3 = 0xAAAAAAAAAAAAAAABULL, p = 1; for (int l = 0; l < 64; l++) { p *= inv3; inv3p[l] = p; }
  S[0] = 0; dfs(0, 0, 0); double P = (double)np;
  printf("J=%d sigma=%d t=%d m=%d |P|=%ld\n", J, sg, t, m, np);
  double two_m = ldexp(1.0, m);
  for (int u = 0; u <= umax && u < m; u++) {
    long H = 1L << u; double tot = 0; long cnt = 0;
    for (int sgn = 0; sgn < 2; sgn++) {
      double complex *acc = calloc(H, sizeof(double complex));
      for (long k = 0; k < np; k++) { double z = (double)Z[k] / two_m; if (sgn) z = -z;
        double complex w = cexp(2 * M_PI * I * z), c = cexp(2 * M_PI * I * z * H);
        for (long x = 0; x < H; x++) { acc[x] += c; c *= w; } }
      for (long x = 0; x < H; x++) { long lam = H + x; if (lam % (1L << t) == 0) continue; tot += creal(acc[x] * conj(acc[x])); cnt++; }
      free(acc); }
    double exact = tot / cnt / (P * P);
    double best = 1;
    for (int N = 0; N <= J; N++) { double r = 0; for (int i = 0; i < N; i++) r += ldexp(1.0, bb[i]) / pow(3, i + 1);
      if (N && log2(2 * r) + N * AL > m) break;
      double mu = N ? ceil(r) : 1, kap = mu * (1 + 2 * pow(3, N) * (1 + N * log(3)) / (double)H), T = 0;
      for (int s = 0; s <= bb[N]; s++) if (f[N][s] > 0 && g[N][s] > 0) T += g[N][s] * fmin(f[N][s], sqrt(kap * f[N][s]));
      double v = (T / P) * (T / P); if (v < best) best = v; }
    best /= (1 - ldexp(1.0, -t));
    printf("u=%2d exact a_u=%.3e  C3 bound=%.3e  %s\n", u, exact, best, exact <= best ? "ok" : "VIOLATION");
  }
  return 0;
}
