"""Exact check: for which shells sigma <= floor(j*alpha) does the ShapeTail certificate
  j * 3^(j/2) * 2^(sigma + e) <= 2^(j/2) * 3^T * C(sigma-1, j-1),  T = floor(31j/100), e = floor(j/300)
still hold?  (shapeTail_of_arith allows any j <= sigma <= b(j); the Lean proof only instantiates the top shell.)
COMPUTATIONAL guidance only; exact integers."""
from math import comb
def top(j): return (3**j).bit_length() - 1
for j in (300, 600, 1200, 2400):
    T, e = 31 * j // 100, j // 300
    ok = [s for s in range(j, top(j) + 1)
          if j * 3**(j // 2) * 2**(s + e) <= 2**(j // 2) * 3**T * comb(s - 1, j - 1)]
    lo = min(ok) if ok else None
    contiguous = ok == list(range(lo, top(j) + 1)) if ok else False
    print(f"j={j}: top shell {top(j)} ({top(j)/j:.4f} j); certificate holds for sigma in [{lo}, {top(j)}]"
          f" = [{lo/j:.4f} j, top], contiguous={contiguous}")
