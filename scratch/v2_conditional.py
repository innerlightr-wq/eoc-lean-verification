"""Is the apparent decay of G_max(H) an arithmetic ceiling or a sampling artifact?

Test: the empirical conditional tail of v2(a-u) given the pre-failure budget bin.
If that tail is essentially H-independent, then a finite-sample maximum necessarily
looks like  max v2 ~ c*log2(n(H)),  and since n(H) decays geometrically while
delta_fail ~ H grows, maxG(H) ~ c*log2 n(H) - H decays linearly FOR FREE.
That would mean the finite data cannot distinguish regimes (70)/(71)/(72) at all.

NOTE (Gate 24): these are empirical frequencies in a finite, non-uniform sample.
They are NOT probabilities of cylinders and carry no measure-theoretic force.
"""
import math, sys
sys.path.insert(0, 'scratch')
from two_criteria import scan

pairs = []
for m0 in range(3, 200001, 2):
    try: pairs += scan(m0, 50)
    except Exception: pass

bins = {}
for H, au, delta, lu in pairs:
    bins.setdefault(int(H), []).append(au)

print("empirical conditional tail  #{v2(a-u) >= q} / n, per budget bin")
print(f"{'Hbin':>5} {'n':>7} " + " ".join(f"q>={q:<2d}" for q in range(1, 9)) + f" {'maxv2':>6} {'lg n':>6} {'ratio':>6}")
for b in sorted(bins):
    v = bins[b]; n = len(v)
    if n < 20: continue
    tail = [sum(1 for x in v if x >= q)/n for q in range(1, 9)]
    mx = max(v); lg = math.log2(n)
    print(f"{b:>5} {n:>7} " + " ".join(f"{t:5.3f}" for t in tail) + f" {mx:>6d} {lg:>6.2f} {mx/lg:>6.3f}")

allv = [au for H,au,d,lu in pairs]
n = len(allv)
print(f"\npooled n={n}, mean v2 = {sum(allv)/n:.4f}, max = {max(allv)}")
print("pooled tail:", " ".join(f"q>={q}:{sum(1 for x in allv if x>=q)/n:.4f}" for q in range(1,11)))
