"""Third independent check of dim C(1,2^8): exact characteristic polynomial of the AL13 Algorithm-A adjacency matrix
(integer Berkowitz / Faddeev-LeVerrier with Fractions), Perron root by bisection with exact sign evaluation."""
from fractions import Fraction as F
import math
from automata import build_stationary
def charpoly(A):
    n=len(A); M=[[F(0)]*n for _ in range(n)]; c=[F(1)]+[F(0)]*n
    I=[[F(int(i==j)) for j in range(n)] for i in range(n)]
    Mk=[[F(0)]*n for _ in range(n)]
    for k in range(1,n+1):
        # M_k = A M_{k-1} + c_{k-1} I ; c_k = -tr(A M_k)/k
        AM=[[sum(A[i][l]*Mk[l][j] for l in range(n) if A[i][l]) for j in range(n)] for i in range(n)]
        Mk=[[AM[i][j]+(c[k-1] if i==j else 0) for j in range(n)] for i in range(n)]
        AMk=[[sum(A[i][l]*Mk[l][j] for l in range(n) if A[i][l]) for j in range(n)] for i in range(n)]
        c[k]=-sum(AMk[i][i] for i in range(n))/k
    return [int(x) for x in c]   # det(xI - A) = sum c_k x^{n-k}
order, edges = build_stationary([256])
idx={s:i for i,s in enumerate(order)}; n=len(order)
A=[[0]*n for _ in range(n)]
for s in order:
    for d,t in edges[s]: A[idx[s]][idx[t]]+=1
cp=charpoly(A)
def ev(x): return sum(F(ck)*x**(n-k) for k,ck in enumerate(cp))
lo,hi=F(13,10),F(15,10)
assert ev(lo)*ev(hi)<0
for _ in range(40):
    mid=(lo+hi)/2
    if ev(lo)*ev(mid)<=0: hi=mid
    else: lo=mid
# confirm no real root above hi (Perron root is the largest real root; check sign up to 2)
xs=[hi+F(k,1000) for k in range(1,701)]
assert all(ev(x)>0 for x in xs)
beta=float(lo)
nz=[(n-k,ck) for k,ck in enumerate(cp) if ck]
print("states:",n)
print("det(xI-A) =", " + ".join(f"({ck})x^{e}" for e,ck in nz))
print(f"largest real root in [1.3,2]: beta = {beta:.9f}; dim = log3 beta = {math.log(beta,3):.6f}")
print("AL13 Table 5.2 reports 0.287416 (beta = 3^0.287416 = %.6f)" % 3**0.287416)
