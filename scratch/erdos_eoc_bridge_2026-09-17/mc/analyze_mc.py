"""Analyse Haar-window MC: danger probability, quenched moments E[val^beta], Chernoff exponents.
c_emp(K)  = -log3 P(val > 2^{K/5}) / K
c_ch(K)   = max_beta [beta*K/5*log3 2 - log3 E[val^beta]] / K   (empirical Markov bound, beta in grid)
Lambda(beta) slope per K from linear fit of log3 E[val^beta] over K >= 8."""
import math, glob, sys
BETAS=[0.5,1,1.5,2,2.5,3,4,5,6,8]
L2=math.log(2,3)
for eta in (54,108):
    agg={}
    for f in glob.glob(f'out_{eta}_*.txt'):
        for line in open(f):
            if not line.startswith('K '): continue
            t=line.split(); K=int(t[1]); n=int(t[3]); d=int(t[5])
            mom=list(map(float,t[7:17])); hist=list(map(int,t[18:418]))
            a=agg.setdefault(K,[0,0,[0.0]*10,[0]*400])
            a[0]+=n; a[1]+=d
            for i in range(10): a[2][i]+=mom[i]
            for i in range(400): a[3][i]+=hist[i]
    print(f"=== eta = 1/{eta} ===   (n per K = {agg[2][0]})")
    print(" K   P(danger)   c_emp   " + "  ".join(f"L({b})" for b in BETAS[1:6]) + "   c_chernoff(beta*)")
    rows=[]
    for K in sorted(agg):
        n,d,mom,hist=agg[K]
        P=d/n; cemp=(-math.log(P,3)/K) if d>0 else float('nan')
        logm=[math.log(mom[i]/n,3)/K for i in range(10)]
        ch=max((BETAS[i]*L2/5 - logm[i], BETAS[i]) for i in range(10))
        rows.append((K,logm))
        print(f"{K:2d}  {P:.3e}  {cemp:6.3f}  " + "  ".join(f"{logm[i]:.4f}" for i in range(1,6)) + f"   {ch[0]:.3f} (beta={ch[1]})")
    # asymptotic slopes of log3 E[val^beta] between K=12 and K=24
    k1,k2=12,24
    print(" slope of log3 E[val^beta] per K (K=12->24), and Chernoff exponent from slopes:")
    best=(-9,0)
    for i,b in enumerate(BETAS):
        m1=agg[k1][2][i]/agg[k1][0]; m2=agg[k2][2][i]/agg[k2][0]
        sl=(math.log(m2,3)-math.log(m1,3))/(k2-k1)
        c=b*L2/5-sl
        best=max(best,(c,b))
        print(f"   beta={b}: Lambda~{sl:.4f}  c={c:.4f}")
    print(f"   best slope-Chernoff c = {best[0]:.4f} at beta={best[1]}  (MC moments for beta>=4 are dominated by rare samples: unreliable)")
