"""Part XVIII: tail of maximal-triangle sizes met by a band of corridors (offsets 0..W-1) at eta = 1/54."""
import math, random, sys
sys.argv = ['x', sys.argv[1], sys.argv[2], '0.0185', 'corridor']
exec(open('triangles.py').read().split('rxi = ')[0])
random.seed(5); Wband = int(sys.argv[2]) if False else 12
from collections import Counter
for name, xi in (("true", 1), ("random", random.randrange(1, 3 ** (J + 5)) | 1)):
    tri = {}
    for off in range(Wband):
        for b in range(1, J + 1):
            a = m - round(AL * b) + off
            if a >= 1 and abs(U(xi, a, b)) < eta:
                A = apex(xi, a, b); tri[A[:2]] = A[2]
    sz = list(tri.values()); n = len(sz)
    print(f"J={J} {name}: {n} triangles; P(size>=r): " + " ".join(f"{r}:{sum(s >= r for s in sz) / n:.3f}" for r in (0.5, 1, 2, 3, 4, 5, 6, 8)) + f"  max={max(sz):.2f}  (random-model e^-r)")
