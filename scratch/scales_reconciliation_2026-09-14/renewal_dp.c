// Renewal functions U (strict ascending ladder heights) and Uhat (strict descending, as depths) of
// the PDF's auxiliary walk: xi = +1 w.p. beta/a, -beta w.p. 1/a, a = log2 3, beta = a - 1.
// Duality (PDF (I4)) + "value determines time" (irrational beta) give, for each lattice point
// (u east, v north), h = v - beta u:
//   atom of U    at h > 0 : P(D_1..D_t > 0, D_t = h), t = u + v;
//   atom of Uhat at w = -h > 0 : P(D_1..D_t < 0, D_t = -w);   plus the unit atom at 0 for both.
// Paths are monotone in (u, v), so a grid DP truncated at u <= U0 is EXACT for every atom with
// u <= U0 (no truncation in v is involved). Tail u > U0 is removed by Richardson extrapolation in
// U0^{-1/2} (local-limit decay t^{-3/2} per atom, PDF Lemma 8.10), using cutoffs U0/4, U0.
// usage: ./renewal_dp U0 HUP HDN < queries ; query lines: "U x" (right value U(x)) or "L x"
// (left limit Uhat(x-)). Output per query: value at cutoff U0/4, U0/2, U0 and extrapolated.
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
typedef struct { double h, p; int u; } atom;
static int cmp(const void *a, const void *b) {
  double x = ((const atom *)a)->h, y = ((const atom *)b)->h;
  return (x > y) - (x < y);
}
static atom *A, *B;
static long nA = 0, nB = 0, capA, capB;
static void push(atom **X, long *n, long *cap, double h, double p, int u) {
  if (*n == *cap) { *cap = *cap * 2 + 1024; *X = realloc(*X, sizeof(atom) * *cap); }
  (*X)[(*n)++] = (atom){h, p, u};
}
int main(int argc, char **argv) {
  const double a = log2(3.0), beta = a - 1.0, pu = beta / a, pe = 1.0 / a;
  int U0 = atoi(argv[1]);
  double HUP = atof(argv[2]), HDN = atof(argv[3]);
  long V0 = (long)floor(beta * U0 + HUP) + 2;
  double *prev = calloc(V0 + 1, sizeof(double)), *cur = calloc(V0 + 1, sizeof(double));
  // ---- ascending: D > 0 after the origin
  for (int u = 0; u <= U0; u++) {
    long vlo = (u == 0) ? 0 : (long)floor(beta * u) + 1;
    for (long v = 0; v < vlo && v <= V0; v++) cur[v] = 0;
    for (long v = vlo; v <= V0; v++) {
      double x;
      if (u == 0) x = (v == 0) ? 1.0 : cur[v - 1] * pu;
      else x = prev[v] * pe + (v > vlo ? cur[v - 1] * pu : 0.0);
      cur[v] = x;
      double h = v - beta * u;
      if (h <= HUP && x > 0) push(&A, &nA, &capA, (u == 0 && v == 0) ? 0.0 : h, x, u);
    }
    double *t = prev; prev = cur; cur = t;
  }
  // ---- descending: D < 0 after the origin (w = beta u - v > 0)
  long V1 = (long)ceil(beta * U0) + 2;
  free(prev); free(cur);
  prev = calloc(V1 + 1, sizeof(double)); cur = calloc(V1 + 1, sizeof(double));
  for (int u = 0; u <= U0; u++) {
    long vhi = (u == 0) ? 0 : (long)ceil(beta * u) - 1;  // v < beta u (beta u never integer)
    for (long v = 0; v <= V1; v++) {
      double x = 0.0;
      if (v <= vhi) {
        if (u == 0) x = 1.0;
        else x = (v <= ((u - 1 == 0) ? 0 : (long)ceil(beta * (u - 1)) - 1) ? prev[v] * pe : 0.0)
                 + (v > 0 ? cur[v - 1] * pu : 0.0);
      }
      cur[v] = x;
      if (v <= vhi) {
        double w = beta * u - v;
        if (w <= HDN && x > 0) push(&B, &nB, &capB, (u == 0) ? 0.0 : w, x, u);
      }
    }
    double *t = prev; prev = cur; cur = t;
  }
  qsort(A, nA, sizeof(atom), cmp);
  qsort(B, nB, sizeof(atom), cmp);
  fprintf(stderr, "atoms: ascending %ld, descending %ld\n", nA, nB);
  char kind;
  double q;
  int cut[3] = {U0 / 4, U0 / 2, U0};
  while (scanf(" %c %lf", &kind, &q) == 2) {
    atom *X = (kind == 'U') ? A : B;
    long n = (kind == 'U') ? nA : nB;
    double s[3] = {0, 0, 0};
    for (long i = 0; i < n; i++) {
      double h = X[i].h;
      int in = (kind == 'U') ? (h <= q + 1e-9) : (h < q - 1e-9);
      if (!in) break;
      for (int k = 0; k < 3; k++) if (X[i].u <= cut[k]) s[k] += X[i].p;
    }
    double ext = 2 * s[2] - s[0];  // kills the U0^{-1/2} tail term
    printf("%c %.10f  %.8f %.8f %.8f  ext %.8f\n", kind, q, s[0], s[1], s[2], ext);
  }
  return 0;
}
