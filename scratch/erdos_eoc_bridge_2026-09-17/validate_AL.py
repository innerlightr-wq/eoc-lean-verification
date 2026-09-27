"""Validate the automaton code against every numerical table in AL13 (arXiv:1308.3133) and ABL15 (arXiv:1508.05967)."""
import math
from automata import dim_C, build_stationary, count_words

def row(name, Ms, paper_dim=None, paper_vertices=None, paper_beta=None):
    d, nv, beta = dim_C(Ms)
    ok = []
    if paper_dim is not None: ok.append(abs(d - paper_dim) < 2e-6)
    if paper_vertices is not None: ok.append(nv == paper_vertices)
    if paper_beta is not None: ok.append(abs(beta - paper_beta) < 2e-6)
    flag = 'OK ' if all(ok) else 'MISMATCH'
    print(f"{flag} {name:22s} vertices={nv:6d} beta={beta:.6f} dim={d:.6f}  paper: dim={paper_dim} vert={paper_vertices} beta={paper_beta}")
    return all(ok)

allok = True
print("== AL13 examples ==")
allok &= row("C(1,7)", [7], 0.438018, 4)
allok &= row("C(1,19)", [19], 0.347934, 8, 1.465571)
allok &= row("C(1,7,19)", [7, 19], 0.347934)
allok &= row("C(1,43) dim 0", [43], 0.0)
allok &= row("C(1,49)", [49], 0.0)   # AL05: countably infinite => dim 0
print("== AL13 Table 4.1: L_k = (1^k)_3 (k vertices) ==")
for k, (b, dd) in enumerate([(2.0, .630929), (1.618033, .438018), (1.465571, .347934), (1.380278, .293358), (1.324718, .255960), (1.285199, .228392), (1.255423, .207052), (1.232055, .189948), (1.213150, .175877)], start=1):
    L = (3 ** k - 1) // 2
    if k == 1:
        continue  # L_1 = 1: C(1,1) = Sigma, the 2-vertex/1-vertex convention differs
    allok &= row(f"C(1,L_{k}={L})", [L], dd, k, b)
print("== AL13 N_k = 3^k+1 (2^k vertices, dim log3 phi) ==")
for k in range(1, 9):
    allok &= row(f"C(1,N_{k})", [3 ** k + 1], 0.438018, 2 ** k)
print("== AL13 Table 5.2: powers of two ==")
for a, dd in [(2, .438018), (4, .255960), (6, .278002), (8, .287416), (10, .215201), (12, .244002), (14, .267112)]:
    allok &= row(f"C(1,2^{a})", [2 ** a], dd)
for combo, dd in [((2, 4), 0.0), ((2, 6), 0.0), ((2, 8), .228392), ((2, 10), 0.0), ((4, 6), 0.0), ((4, 8), 0.0), ((4, 10), 0.0), ((6, 8), 0.0), ((6, 10), 0.0), ((8, 10), 0.0), ((2, 8, 12), 0.0), ((2, 8, 14), 0.0), ((2, 8, 16), 0.0)]:
    allok &= row("C(1," + ",".join(f"2^{a}" for a in combo) + ")", [2 ** a for a in combo], dd)
print("== ABL15 Table 2.1: P_k = 2*3^k+1 ==")
for k, (nv, b, dd) in enumerate([(4, 1.618033, .438018), (8, 1.465571, .347934), (16, 1.380278, .293358), (32, 1.324718, .255960), (64, 1.370957, .287191), (128, 1.388728, .298913), (256, 1.392067, .301010), (512, 1.387961, .298408)], start=1):
    allok &= row(f"C(1,P_{k}={2*3**k+1})", [2 * 3 ** k + 1], dd, nv, b)
print("== ABL15 Q_k = 3^{2k}-3^k+1 (4^k vertices, dim log3 phi, k>=2) ==")
for k in range(2, 6):
    allok &= row(f"C(1,Q_{k})", [3 ** (2 * k) - 3 ** k + 1], 0.438018, 4 ** k)
print("== ABL15 Table 7.1 ==")
for M, nv, b, dd in [(10, 4, 1.618033, .438018), (16, 5, 1.324718, .255960), (19, 8, 1.465571, .347934), (73, 16, 1.618033, .438018), (34, 8, 1.324718, .255960), (46, 10, 1.112776, .097266), (61, 14, 1.570147, .410672), (64, 14, 1.357193, .278004), (70, 14, 1.360632, .280308), (91, 9, 1.465571, .347934), (97, 16, 1.380277, .293356), (100, 17, 1.354948, .276497), (142, 20, 1.276393, .222133), (145, 21, 1.0, 0.0), (151, 20, 1.227525, .186599), (172, 22, 1.288329, .230606), (178, 25, 1.345528, .270148), (181, 22, 1.324718, .255960), (196, 24, 1.383785, .295666), (208, 25, 1.290893, .232415)]:
    allok &= row(f"C(1,{M})", [M], dd, nv, b)
print("== Lagarias 2005 Thm 1.5(3) / ABL: C(1,4,256) ==")
allok &= row("C(1,4,256)", [4, 256], 0.228392)
print("ALL OK" if allok else "SOME MISMATCH")
