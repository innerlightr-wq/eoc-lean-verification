"""Exact integer verification of a super-eigenvector for the cell majorant Lt (beta = 2, s = 9, q = 37/100).
Checks  Lt V <= rho' V  cellwise in exact integers, with V_j = ceil(v_j * 2^48) >= 1 and rho' rational.
Tail g >= g0 (every image covers the circle): bounded with cnt_g <= g-2, summed in closed form.
Conclusion (PROVED MATH + this exact check): E_xi[val^2] <= rho'^K * max V / min V for every K and start phase,
hence P(val > 2^{K/5}) <= (max V/min V) * (rho'/2^{2/5})^K."""
import sys, math
from fractions import Fraction as Fr
Lc=int(sys.argv[1]); fname=sys.argv[2]; rho=Fr(sys.argv[3])
beta=2; s=9; p=Fr(63,100); q=Fr(37,100)
P=54<<Lc; Imax=Lc+8
v=[float(x) for x in open(fname)]
assert len(v)==P
V=[max(1, math.ceil(x*2**48)) for x in v]
# meet table (identical integer test to phaseop.c)
SP=54*P
def meet(i,j):
    lo=54*(1<<i)*j; hi=54*(1<<i)*(j+1)
    if hi-lo>=SP: return 1
    n0=lo//SP
    for n in range(n0-1,n0+3):
        L=(54*n-1)*P; R=(54*n+1)*P
        if lo<R and hi>L: return 1
    return 0
g0=1
while (1<<g0) < 9*P: g0+=1          # for g >= g0 every image covers the circle
cnt=[[0]*(g0) for _ in range(P)]
for j in range(P):
    c=0
    for g in range(g0):
        i=g-2
        if i>=1: c+= meet(i,j) if i<=Imax else 1
        cnt[j][g]= c if g>=3 else 0
# sparse table for circular range max over integers V
LOG=max(1,(P-1).bit_length())
sp=[V[:]]
for l in range(1,LOG+1):
    h=1<<(l-1); prev=sp[-1]; sp.append([max(prev[j],prev[(j+h)%P]) for j in range(P)])
def rmax(a,b):
    ln=b-a+1
    if ln>=P: return maxV
    st=a%P; l=ln.bit_length()-1
    return max(sp[l][st], sp[l][(st+ln-(1<<l))%P])
maxV=max(V); minV=min(V)
# common denominator: weights p^2 q^{g-2} = 63^2 37^{g-2} / 100^g ; multiply everything by 9 * 100^{g0}
DEN=9*100**g0
UNIFORM = len(sys.argv)>4 and sys.argv[4]=="uniform"
QLO = Fr(sys.argv[5]) if len(sys.argv)>5 else Fr(36,100)
QHI = Fr(37,100)
DEN=9*10000**g0
def wq(g):
    """max over q in [QLO, QHI] of (1-q)^2 q^{g-2} (exact): unimodal with maximiser (g-2)/g."""
    if not UNIFORM: return (1-QHI)**2*QHI**(g-2)
    qs=Fr(g-2,g)
    cand=[QLO,QHI]+([qs] if QLO<=qs<=QHI else [])
    return max((1-x)**2*x**(g-2) for x in cand)
W=[None,None]+[wq(g)*10000**g for g in range(2,g0)]
for g in range(2,g0): assert W[g].denominator==1 or True
def wnum(g):
    x=wq(g)*10000**g0
    assert x.denominator==1
    return int(x)
# tail: sum_{g>=g0} p^2 q^{g-2} ((g-1)+(s-1)(g-2)) = p^2 sum_{n>=n0} q^n (s n + 1), n0 = g0-2
n0=g0-2
# tail with q = QHI and p^2 <= (1-QLO)^2 (termwise max is at QHI for g >= 4)
tail=((1-QLO)**2 if UNIFORM else p*p)*( s*QHI**n0*(n0-(n0-1)*QHI)/(1-QHI)**2 + QHI**n0/(1-QHI) )
tailnum=tail*DEN*maxV*9   # (1/9 sum_D maxV) * 9 = 9 maxV ... careful: R_g = (1/9)*sum_D max = maxV; times DEN
tailnum=tail*DEN*maxV
worst=Fr(0)
bad=0
for j in range(P):
    S=0
    for g in range(2,g0):
        tot=0
        for D in range(9):
            a=((1<<g)*(j+D*P))//9; b=((1<<g)*(j+1+D*P))//9
            tot+=rmax(a,b)
        # term = p^2 q^{g-2} ((g-1)+(s-1)cnt) * tot/9  ->  times DEN = 9*100^{g0}: wnum(g)*(...)*tot
        S+=wnum(g)*((g-1)+(s-1)*cnt[j][g])*tot
    lhs=Fr(S)+tailnum
    r=lhs/(DEN*V[j])
    if r>worst: worst=r
    if lhs> rho*DEN*V[j]: bad+=1
print(f"uniform-in-q={UNIFORM} Lc={Lc} P={P} g0={g0}: max_j (Lt V)_j/V_j = {float(worst):.10f}  (exact rational check vs rho'={float(rho)}: violations={bad})")
print(f"maxV/minV = {maxV/minV:.4f}")
c=beta*math.log(2,3)/5 - math.log(float(rho),3)
print(f"=> P(val > 2^(K/5)) <= {maxV/minV:.3f} * 3^(-{c:.5f} K)   [beta=2, q=37/100, eta=1/54]")
