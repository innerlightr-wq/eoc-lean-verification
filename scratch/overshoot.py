"""GATE 29/AD: the exit-overshoot process.  At the first drift exit tau,
   descent happens iff R_tau > E_tau.  How close does R_tau - E_tau get to 0?

   R_tau > 0 with S_tau integer forces R_tau >= 1 - {alpha*tau}, so strictness
   (tau_0 < sigma) needs {alpha*tau} > 1 - E_tau, with E_tau tiny.
"""
import math
alpha = math.log2(3)
def v2(n):
    r=0
    while n&1==0: n>>=1; r+=1
    return r

rows=[]
for m0 in range(3, 400001, 2):
    mi=m0; S=0; E=0.0; n=0
    while n < 5000:
        t=3*mi+1; d=v2(t)
        E += math.log2(1+1/(3*mi))
        S += d; mi = t >> d; n += 1
        R = S - alpha*n
        if R > 0:
            rows.append((R-E, m0, n, R, E, (alpha*n)%1.0, mi<m0))
            break
        if mi==1: break

rows.sort()
print(f"seeds with a drift exit: {len(rows)}")
print(f"{'m':>8} {'tau':>5} {'R_tau':>9} {'E_tau':>8} {'R-E':>9} {'frac(a*tau)':>12} {'descended?':>11}")
for g,m,t,R,E,fr,des in rows[:10]:
    print(f"{m:>8} {t:>5} {R:>9.5f} {E:>8.5f} {g:>9.5f} {fr:>12.5f} {str(des):>11}")
print()
print(f"minimum of R_tau - E_tau over all seeds: {rows[0][0]:.6f}")
print(f"number with R_tau <= E_tau (i.e. tau_0 < sigma): {sum(1 for r in rows if r[0] <= 0)}")
print(f"maximum E_tau observed: {max(r[4] for r in rows):.5f}")
print(f"minimum R_tau observed: {min(r[3] for r in rows):.5f}")
print()
print("Why the coincidence: R_tau > 0 with S_tau integral forces R_tau >= 1 - frac(alpha*tau).")
print("So tau_0 < sigma needs frac(alpha*tau) > 1 - E_tau.  With E_tau <= %.3f that needs" % max(r[4] for r in rows))
print("frac(alpha*tau) > %.3f, and additionally the orbit must stay confined until tau." % (1-max(r[4] for r in rows)))
ntau = {}
for g,m,t,R,E,fr,des in rows: ntau[t]=ntau.get(t,0)+1
print("\ndistribution of tau_0 (top 10):", sorted(ntau.items(), key=lambda kv:-kv[1])[:10])
