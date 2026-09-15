"""App I.3 literal test: r_min(N,c) = least odd seed that is c-confined for N steps
(= least realizer over C_N(c)).  Under H0 (placement carries no residual phase beyond the ensemble),
P(r_min(N) > Y) = exp(-theta (Y/2) p_N(c)), theta = 1/2.92 (prefix-interval extremal index), so
E_N := theta r_min(N) p_N / 2 ~ Exp(1) and log2 r_min(N) = -log2 p_N + 1 - log2 theta + log2 E_N.
The ensemble phase of p_N enters log2 r_min only through log2 L_c(phi_N) (a few hundredths of a bit)."""
import json, re, sys
from math import log2, exp
A = log2(3)
H2 = lambda p: -p * log2(p) - (1 - p) * log2(1 - p)
I0 = A * (1 - H2(1 / A))
theta = 1 / 2.92
def records(files, key):
    rec = []
    for fn in files:
        t = open(fn).read()
        rec += [(int(a), int(b)) for a, b in re.findall(r"(\d+):(\d+)", re.search(key + r"(.*)", t).group(1))]
    return sorted(rec)
sets = {0: records(["../pair_valuation_2026-09-14/hist_2p32.out"], r"EXIT_RECORDS U=0:") +
           records(["../pair_valuation_2026-09-14/glide_sieve_32_36.out", "../pair_valuation_2026-09-14/glide_sieve_36_40.out"], r"RECORDS:"),
        1: records(["surv_U1_2p35.log"], r"RECORDS:"), 2: records(["surv_U2_2p35.log"], r"RECORDS:")}
T = json.load(open("pn_table.json"))
for c, rec in sets.items():
    rec.sort()
    lp = {r["N"]: r["lP"] for r in T[str(c)]}
    Nmax = max(e for _, e in rec)
    rows = []
    for N in range(40, Nmax):
        rm = min(mu for mu, e in rec if e > N)
        LE = log2(rm) + lp[N] - 1 + log2(theta)
        Lam = lp[N] + I0 * N + 1.5 * log2(N)
        rows.append((N, (N * A) % 1, rm, LE, Lam))
    le = [r[3] for r in rows]
    mean = sum(le) / len(le)
    changes = sum(1 for i in range(1, len(rows)) if rows[i][2] != rows[i - 1][2])
    print(f"c={c}: N in [40,{Nmax}), {changes + 1} distinct record holders; lambda_N = log2 r_min/N at N={rows[-1][0]}: "
          f"{log2(rows[-1][2]) / rows[-1][0]:.4f} (I0 = {I0:.4f})")
    print(f"   mean log2(theta r_min p_N / 2) = {mean:+.3f}  (Exp(1) prediction -0.833, sd 1.85 per independent record)")
    ws = []
    for w in range(5):
        sel = [r[3] for r in rows if w / 5 <= r[1] < (w + 1) / 5]
        ws.append(sum(sel) / len(sel))
    print("   phase-window means (5 windows):", " ".join(f"{x:+.3f}" for x in ws),
          f" | spread of the ensemble phase factor log2 L_c: {max(r[4] for r in rows[-60:]) - min(r[4] for r in rows[-60:]):.3f} bits")
