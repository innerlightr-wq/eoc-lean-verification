from math import log2
A = log2(3)

def orbit(m):
    """accelerated orbit until it hits 1; returns list of (m_n, d_n) and the m-sequence"""
    ms=[m]; ds=[]
    while ms[-1]!=1:
        x=ms[-1]; y=3*x+1; d=0
        while y%2==0: y//=2; d+=1
        ds.append(d); ms.append(y)
        if len(ms)>100000: break
    return ms, ds

def Sseq(ds):
    S=[0]
    for d in ds: S.append(S[-1]+d)
    return S

# ---------- 1. entry lemma: at every re-entry d_{a-1}=1 and 0 <= c-R_a < A-1 ----------
def check_entry(c, lo=3, hi=60001):
    bad_digit=0; bad_band=0; nre=0; worst=0.0
    for m in range(lo,hi,2):
        ms,ds=orbit(m); S=Sseq(ds); n_star=len(ms)-1
        pw=[2**s for s in S]; thr=[(2**c)*3**n for n in range(len(S))]
        inC=[pw[n]<=thr[n] for n in range(n_star+1)]
        for n in range(1,n_star+1):
            if (not inC[n-1]) and inC[n]:
                nre+=1
                if ds[n-1]!=1: bad_digit+=1
                R = S[n]-n*A; ca = c-R
                if not (0<=ca<A-1+1e-12): bad_band+=1
                worst=max(worst,ca)
    return nre,bad_digit,bad_band,worst

for c in (0,1,2,5):
    print("c=%d  re-entries=%6d  d!=1: %d   band violations: %d   max c-R_a=%.6f  (A-1=%.6f)"%((c,)+check_entry(c)+(A-1,)))
