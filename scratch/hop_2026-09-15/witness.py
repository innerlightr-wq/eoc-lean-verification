"""Part I-II: exact search for distinct-triangle consecutive black pairs (a'+d, b) -> (a', b+1) at threshold eta = 1/E.
Distinct <=> y(a', b+1) != 2^d y(a'+d, b).  Theorem: distinct => (2^d + 3) eta > 1.  Reports the minimal d found."""
import sys
E = int(sys.argv[1]) if len(sys.argv) > 1 else 54
A, B = 600, 60
ys = {}
def Y(a, b):
    if (a, b) not in ys:
        q = 3 ** b; v = pow(2, -a, q); ys[(a, b)] = v - q if v > q // 2 else v
    return ys[(a, b)]
blk = lambda a, b: E * abs(Y(a, b)) < 3 ** b
dmin_thm = min(d for d in range(1, 40) if (2 ** d + 3) > E)      # (2^d+3)/E > 1
found = {}; first = {}
for b in range(1, B):
    for a1 in range(1, A):
        for d in range(1, 16):
            if blk(a1 + d, b) and blk(a1, b + 1) and Y(a1, b + 1) != 2 ** d * Y(a1 + d, b):
                found[d] = found.get(d, 0) + 1; first.setdefault(d, (a1, b, Y(a1 + d, b), Y(a1, b + 1)))
print(f"eta = 1/{E}: theorem d_min = {dmin_thm}; distinct pairs found by d (a' < {A}, b < {B}): {dict(sorted(found.items()))}")
d0 = min(found) if found else None
if d0:
    a1, b, y0, y1 = first[d0]
    print(f"  witness d={d0}: cells ({a1 + d0},{b}) and ({a1},{b + 1}); y = {y0}, y' = {y1}, 3^b = {3 ** b}; "
          f"|y|/3^b = {abs(y0) / 3 ** b:.5f} < 1/{E}, |y'|/3^(b+1) = {abs(y1) / 3 ** (b + 1):.5f} < 1/{E}; y' - 2^d y = {y1 - 2 ** d0 * y0} (= {(y1 - 2 ** d0 * y0) // 3 ** b} * 3^b)")
