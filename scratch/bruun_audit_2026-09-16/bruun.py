"""Independent reproduction of the counting and class structure in R. Bruun, arXiv:2105.11334v6.

Bruun's tiles are Terras steps: E-tile  n -> n/2  (n even),  OE-tile  n -> (3n+1)/2  (n odd).
After k tiles with s OE-tiles,  T^k(n) = (3^s n + c)/2^k  on the residue class n = P (mod 2^k)  (Terras/Everett).
Bruun's IV-class [2^k X - B] is this class (P = 2^k - B the least positive member); his TV-class
[3^s X - B'] is the image  T^k(2^k X - B) = 3^s X - B'.
"Reducing" (Bruun *Converging) at level k: first k with 3^s < 2^k (Terras coefficient stopping time chi = k).
Bruun's membership criterion for the whole class: P_TV < P_IV, i.e. T^k(P) < P (X = 1; monotone in X).

Outputs (stdout):  A. counts G(s) by (i) Bruun's Formula (2a), (ii) lattice-path DP, (iii) residue enumeration,
compared with Bruun's Resultlist 1;  B. per-class check of P_TV < P_IV;  C. unresolved sets D_k (count, density,
least member = threshold values);  D. orbit-level stopping times, chi = sigma, records, Bruun's chi < 3N remark;
E. sample classes (Appendix Alpha), merging example (p. 40), B-dynamics and the terminal residue mod 3^s;
F. the 2-adic chain of -1 and the chain of 27.
"""
import math, sys
from math import comb

ALPHA = math.log2(3)


def rceil(s):                      # least r with 2^r > 3^s  (Bruun Formula (1), exact integer version)
    return (3 ** s).bit_length()


# ---------------- A. counts ----------------
def G_formula(smax):
    """Bruun Formula (2a): G(s) = C(r_s, s) - sum_{s'<s} G(s') C(r_s - r_{s'}, s - s')."""
    G = []
    for s in range(smax + 1):
        r = rceil(s)
        g = comb(r, s) - sum(G[t] * comb(r - rceil(t), s - t) for t in range(s))
        G.append(g)
    return G


def G_paths(smax):
    """Lattice-path DP (independent): count 0/1 words of length r_s with s ones that first satisfy 3^s < 2^k at k = r_s.
    State after k tiles: number of ones; alive iff 3^ones >= 2^k for all prefixes."""
    R = rceil(smax)
    alive = {0: 1}                  # ones -> count, at level k = 0
    first = {}                      # (k, ones) -> count reducing exactly at k
    for k in range(1, R + 1):
        nxt = {}
        for o, c in alive.items():
            for bit in (0, 1):
                o2 = o + bit
                if 3 ** o2 < 2 ** k:
                    first[(k, o2)] = first.get((k, o2), 0) + c
                else:
                    nxt[o2] = nxt.get(o2, 0) + c
        alive = nxt
    return [first.get((rceil(s), s), 0) for s in range(smax + 1)], first


BRUUN_RL1 = [  # s, r, |Red|, |Div|, |Con|, cumulative  (Resultlist 1, p. 32)
    (0, 1, 0, 1, 1, 1), (1, 2, 2, 1, 1, 2), (2, 4, 12, 3, 1, 3), (3, 5, 26, 4, 2, 5), (4, 7, 112, 13, 3, 8),
    (5, 8, 230, 19, 7, 15), (6, 10, 948, 64, 12, 27), (7, 12, 3840, 226, 30, 57), (8, 13, 7740, 367, 85, 142),
    (9, 15, 31300, 1295, 173, 315), (10, 16, 62946, 2114, 476, 791), (11, 18, 253688, 7495, 961, 1752),
    (12, 20, 1018596, 27328, 2652, 4404), (13, 21, 2042496, 46611, 8045, 12449),
    (14, 23, 8202164, 168807, 17637, 30086), (15, 24, 16439602, 290496, 47118, 77204),
    (16, 26, 65946880, 1074149, 87835, 165039), (17, 27, 132069430, 1852478, 295820, 460859),
    (18, 29, 529461000, 6840772, 569140, 1029999), (19, 31, 2120120560, 25841433, 1521655, 2551654),
    (20, 32, 4243284430, 46010008, 5672858, 8224512), (21, 34, 16995829152, 172315631, 11724401, 19948913),
    (22, 35, 34015107106, 306244032, 38387230, 58336143)]


def partA(Kenum):
    print("== A. Counts of reducing classes G(s) (Bruun |*Con(r_s)|)")
    G = G_formula(80)
    Gp, first = G_paths(40)
    ok_fp = all(G[s] == Gp[s] for s in range(41))
    print(f"Formula (2a) == lattice-path DP for s <= 40: {ok_fp}")
    print(f"first reductions only at k = r_s: {all(k == rceil(o) for (k, o) in first)}  (VERIFIED MATH: a crossing needs an E-tile)")
    # Div(r) from DP: alive count at level r
    mism = []
    div = {}
    alive = {0: 1}
    for k in range(1, rceil(22) + 1):
        nxt = {}
        for o, c in alive.items():
            for bit in (0, 1):
                o2 = o + bit
                if 3 ** o2 >= 2 ** k:
                    nxt[o2] = nxt.get(o2, 0) + c
        alive = nxt
        div[k] = sum(alive.values())
    cum = 0
    red = 0
    for (s, r, R_, D_, C_, cum_) in BRUUN_RL1:
        cum += G[s]
        red = 2 ** r - div[r] - G[s]
        row = (rceil(s), red, div[r], G[s], cum)
        if row != (r, R_, D_, C_, cum_):
            mism.append((s, (r, R_, D_, C_, cum_), row))
    print(f"Bruun Resultlist 1 (s <= 22, all 6 columns) reproduced exactly: {not mism}  mismatches: {mism}")
    print("G(s), s = 0..30:", G[:31])
    print("G(s) > 0 for all s <= 80:", all(g > 0 for g in G))
    print("density of unresolved (1 - S) at r_s:",
          ", ".join(f"s={s}:{div[rceil(s)] / 2 ** rceil(s):.6f}" for s in (1, 5, 10, 15, 20, 22)))
    # exponential decay rate of the unresolved density (continue DP further)
    alive = {0: 1}; dens = {}
    for k in range(1, 401):
        nxt = {}
        for o, c in alive.items():
            for bit in (0, 1):
                o2 = o + bit
                if 3 ** o2 >= 2 ** k:
                    nxt[o2] = nxt.get(o2, 0) + c
        alive = nxt
        if k in (50, 100, 200, 400):
            dens[k] = sum(alive.values()) / 2 ** k
    print("unresolved density at k = 50,100,200,400:", {k: f"{v:.3e}" for k, v in dens.items()},
          " per-step ratio 200->400:", f"{(dens[400] / dens[200]) ** (1 / 200):.5f}")
    print("unresolved COUNT |Div(k)| at k = 50,100,200,400 (log2):",
          {k: f"{math.log2(v * 2 ** k):.2f}" for k, v in dens.items()})


# ---------------- B/C/E/F. residue-class tree ----------------
def tree(K):
    """BFS over unresolved classes. node = (P, y, s, c) with n = P (mod 2^k), y = T^k(P), T^k(n) = (3^s n + c)/2^k."""
    level = [(0, 0, 0, 0)]          # k = 0: universe class; P = 0 stands for 2^0 X - 0 (least member 1 handled below)
    stats = []
    bad = []                        # reducing classes whose least member does not drop (P_TV >= P_IV)
    samples = {}
    for k in range(K):
        nxt = []
        con = 0
        for (P, y, s, c) in level:
            for t in (0, 1):
                P2 = P + (t << k)
                y2 = y + t * 3 ** s          # T^k(P2)
                if y2 % 2:
                    y3, s3, c3 = (3 * y2 + 1) // 2, s + 1, 3 * c + 2 ** k
                else:
                    y3, s3, c3 = y2 // 2, s, c
                k3 = k + 1
                Pl = P2 if P2 > 0 else 2 ** k3       # least positive member
                y3l = (3 ** s3 * Pl + c3) // 2 ** k3
                assert (3 ** s3 * Pl + c3) % 2 ** k3 == 0
                if 3 ** s3 < 2 ** k3:
                    con += 1
                    if not (y3l < Pl) and Pl != 1:
                        bad.append((k3, Pl, y3l))
                    if k3 <= 7:
                        samples.setdefault(k3, []).append((Pl, 2 ** k3 - Pl, s3, y3l, 3 ** s3 - y3l, c3))
                else:
                    nxt.append((P2, y3, s3, c3))
        level = nxt
        least = min((P if P > 0 else 2 ** (k + 1)) for (P, _, _, _) in level) if level else None
        stats.append((k + 1, con, len(level), least))
    return stats, bad, samples, level


def stopping(n, cap=100000):
    y, s, k, chi = n, 0, 0, None
    while k < cap:
        if y % 2:
            y = (3 * y + 1) // 2; s += 1
        else:
            y //= 2
        k += 1
        if chi is None and 3 ** s < 2 ** k:
            chi = k
        if y < n:
            return chi, k
    return chi, None


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 26
    NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 6
    partA(K)

    print(f"\n== B/C. Residue-class tree to level k = {K}")
    stats, bad, samples, level = tree(K)
    print(" k  reducing_at_k  unresolved  density      least_unresolved_member")
    for (k, con, und, least) in stats:
        print(f"{k:2d}  {con:12d}  {und:10d}  {und / 2 ** k:.6f}  {least}")
    print(f"reducing classes (k <= {K}) whose least member P does NOT drop below P at step k (P_TV >= P_IV), P != 1: "
          f"{len(bad)} {bad[:5]}")
    print("Hence for these classes every member drops at exactly its coefficient stopping time (COMPUTATIONAL).")

    print("\n== E. Sample reducing classes, k <= 7:  (P_IV, B_IV, s, P_TV, B_TV, c)")
    for k in sorted(samples):
        print(k, sorted(samples[k]))
    # merging example p. 40: 387 = 2^9 X - 125, 391 = 2^9 X - 121
    def Tk(n, k):
        for _ in range(k):
            n = (3 * n + 1) // 2 if n % 2 else n // 2
        return n
    print("merge example (p. 40): T^9(387), T^9(391) =", Tk(387, 9), Tk(391, 9))
    # B-dynamics and terminal residue
    ok = True
    for k in range(1, 15):
        for P in range(1, 2 ** k + 1):
            y, s, c = P, 0, 0
            for i in range(k):
                if y % 2:
                    y = (3 * y + 1) // 2; c = 3 * c + 2 ** i; s += 1
                else:
                    y //= 2
            B = 2 ** k - P
            Bp = 3 ** s - y if y <= 3 ** s else None
            if (3 ** s * B - c) % 2 ** k != 0:
                ok = False
            if (-y) % 3 ** s != (-c * pow(2, -k, 3 ** s)) % 3 ** s:
                ok = False
    print("terminal residue T^k(n) = c * 2^{-k} (mod 3^s) for all classes k <= 14:", ok,
          " (the only appearance of 2^{-a} mod 3^b; Bruun gives no distribution statement for it)")

    print(f"\n== D. Orbit-level stopping times, 2 <= n <= {NMAX}")
    maxratio = (0, None); records = []; best = 0; mism = 0
    for n in range(2, NMAX + 1):
        chi, sig = stopping(n)
        if chi != sig:
            mism += 1
        if chi > best:
            best = chi; records.append((n, chi))
        if chi / n > maxratio[0] and n > 2:
            maxratio = (chi / n, n)
    print("chi(n) != sigma(n) occurrences:", mism)
    print("stopping-time records (n, chi):", records)
    print("max chi(n)/n for 3 <= n <= NMAX:", maxratio)

    print("\n== F. Nested chains")
    # -1 in Z_2: all OE tiles; class 2^k - 1 is unresolved for every k, least member 2^k - 1 -> infinity
    print("all-odd chain (2-adic -1): least members", [2 ** k - 1 for k in range(1, 12)], "... never reducing (3^k >= 2^k)")
    chi27, sig27 = stopping(27)
    print("27: chi = sigma =", chi27, sig27, "-> the class of 27 mod 2^k stays unresolved for k < 59, with least member",
          "27 once 2^k > 27 (k >= 5)")


if __name__ == "__main__":
    main()
