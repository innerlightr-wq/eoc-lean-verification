"""Compare the PDF's renewal-phase predictions (Thms 8.20, 8.22) with the phase-matched exact DP
data of scratch/pair_valuation_2026-09-14/exponent_audit_c*.out.
  rho_shell = N A_N(c,s_N) / C(s_N-1,N-1)   -> rho U(c+beta) Uhat(phi-)                (Thm 8.20)
  rho_tot   = N W_c(N) / C(s_N, N)          -> rho^2 U(c+beta) sum_x (beta/a)^x Uhat((phi+x)-)
                                               = rho F_c(phi)                          (Thm 8.22)
Also a finite-N version (exact shell weights and N/T'_x instead of their limits), which keeps only
the o(1) of Theorem 8.7 as error.  U, Uhat come from renewal_dp (exact grid DP + Richardson).
usage: python3 phase_prediction.py U0"""
import re
import subprocess
import sys
from math import comb, floor, log2
A = log2(3); BETA = A - 1; RHO = 1 / A
U0 = sys.argv[1]
XMAX = 28
rows = {}
for c in range(4):
    for line in open(f"../pair_valuation_2026-09-14/exponent_audit_c{c}.out"):
        m = re.match(r"\s+(\d+)\s+([\d.]+)\s+([\d.]+)\s+\|", line)
        if m:
            rows[(c, int(m.group(1)))] = (float(m.group(2)), float(m.group(3)))
Ns = sorted({N for _, N in rows})
queries = [f"U {c + BETA:.12f}" for c in range(4)]
phis = {N: (N * A) % 1 for N in Ns}
for N in Ns:
    queries += [f"L {phis[N] + x:.12f}" for x in range(XMAX + 1)]
out = subprocess.run(["./renewal_dp", U0, "4", str(XMAX + 2)], input="\n".join(queries),
                     capture_output=True, text=True).stdout.split("\n")
vals = {}
lines = [l for l in out if l.strip()]
assert len(lines) == len(queries)
for q, line in zip(queries, lines):  # outputs come back in query order
    p = line.split()
    vals[q] = (float(p[2]), float(p[4]), float(p[6]))  # (cutoff U0/4, U0, extrapolated)
def U(x): return vals[f"U {x:.12f}"][2]
def Uh(x): return vals[f"L {x:.12f}"][2]
def Uh_raw(x): return vals[f"L {x:.12f}"][1]
print(f"U0={U0}:  U(beta) = {U(BETA):.7f} (alpha = {A:.7f});  U(c+beta)/U(beta) for c=1,2,3: " +
      ", ".join(f"{U(c + BETA) / U(BETA):.5f}" for c in (1, 2, 3)))
print("  extrapolation size (ext - raw at U0), Uhat(phi-) typical:",
      f"{Uh(phis[Ns[0]]) - Uh_raw(phis[Ns[0]]):.2e}")
print(" c     N    phi   | rho_shell obs  pred_lim  pred_finN  rel.err | rho_tot obs  pred_lim  pred_finN  rel.err")
for c in range(4):
    for N in Ns:
        if (c, N) not in rows:
            continue
        rt, rs = rows[(c, N)]
        phi = phis[N]
        sN = floor(N * A) + c
        pl_s = RHO * U(c + BETA) * Uh(phi)
        pf_s = N / (sN - 1) * U(c + BETA) * Uh(phi)
        pl_t = RHO * RHO * U(c + BETA) * sum((BETA / A) ** x * Uh(phi + x) for x in range(XMAX + 1))
        base = comb(sN - 1, N - 1)
        pf_t = (N / sN) * sum(comb(sN - x - 1, N - 1) / base * N / (sN - x - 1) * U(c + BETA) * Uh(phi + x)
                              for x in range(XMAX + 1))
        print(f" {c}  {N:5d}  {phi:.4f} | {rs:9.4f}  {pl_s:8.4f}  {pf_s:8.4f}  {rs / pf_s - 1:+.1e} |"
              f" {rt:9.4f}  {pl_t:8.4f}  {pf_t:8.4f}  {rt / pf_t - 1:+.1e}")
