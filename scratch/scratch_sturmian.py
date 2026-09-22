from fractions import Fraction
from decimal import Decimal, getcontext
getcontext().prec=80
# high-precision alpha = log2 3
A = Fraction(Decimal(3).ln()/Decimal(2).ln())   # ~80 digits, then exact rational
A = Fraction(A).limit_denominator(10**40)
beta = 2-A; gamma = A-1
print("alpha ~ %.15f   beta = 2-alpha ~ %.15f   gamma = alpha-1 ~ %.15f   beta+gamma = %s"
      %(float(A),float(beta),float(gamma),beta+gamma))
c = Fraction(1); N = 200000
# exact rational drift: S_n - n*alpha, digit 2 iff R_n <= c
S = Fraction(0); xs=[]; d=[]
for n in range(N):
    R = S - n*A
    x = R - c
    xs.append(x)
    dn = 2 if x <= 0 else 1
    d.append(dn); S += dn
mn,mx = min(xs), max(xs)
print("\n=== two-sided drift window (c=1, n<%d), EXACT rational arithmetic ==="%N)
print("  min (R_n - c) = %.12f    predicted > -gamma = %.12f  : %s"%(float(mn),float(-gamma), mn > -gamma))
print("  max (R_n - c) = %.12f    predicted <=  beta = %.12f  : %s"%(float(mx),float(beta),  mx <= beta))
print("  so |R_n - c| <= %.12f for ALL n < %d"%(max(abs(float(mn)),abs(float(mx))),N))
bad=sum(1 for n in range(N-1) if xs[n+1] != (xs[n]+beta if xs[n]<=0 else xs[n]-gamma))
print("  rotation identity x_{n+1} = x_n + beta (mod 1) on (-gamma,beta]: %d violations"%bad)
per=[p for p in range(1,2001) if all(d[i]==d[i+p] for i in range(N-p))]
print("  exact periods p <= 2000 of the digit word: %s"%(per if per else "NONE"))
print("\n=== factor complexity (Sturmian <=> exactly L+1 factors of length L) ===")
for L in (1,2,3,4,5,6,8,10,20):
    print("   L=%2d : %3d factors   (Sturmian: %3d)"%(L,len(set(tuple(d[i:i+L]) for i in range(N-L))),L+1))
