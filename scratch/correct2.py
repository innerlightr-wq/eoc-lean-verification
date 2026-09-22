from math import log2
A=log2(3)
def orbit(m):
    ms=[m]; ds=[]
    while ms[-1]!=1:
        x=ms[-1]; y=3*x+1; d=0
        while y%2==0: y//=2; d+=1
        ds.append(d); ms.append(y)
    return ms,ds
def Sq(ds):
    S=[0]
    for d in ds: S.append(S[-1]+d)
    return S

print("=== 4a. carry E_n on the tail at 1 (T(1)=1, d=2, E grows by log2(4/3)) ===")
print("  T(1) = (3*1+1)/2^nu2(4) = 4/4 =", (3*1+1)//4, "   log2(4/3) =", round(log2(4/3),6))
E=0.0
for k in range(1,9): E+=log2(1+1/3); 
print("  E after 8 tail steps at m=1:", round(E,4), "-> E_infty = +infinity on every orbit reaching 1")

print("\n=== 4b. max E_n over CORRIDOR times vs over the WHOLE orbit (c=1) ===")
c=1; mE_corr=0.0; mE_all=0.0; argall=0
for m in range(3,60001,2):
    ms,ds=orbit(m); S=Sq(ds); n_star=len(ms)-1
    Q=1.0
    for n in range(n_star+1):
        En=log2(Q)
        if 2**S[n] <= (2**c)*3**n: mE_corr=max(mE_corr,En)
        if En>mE_all: mE_all=En; argall=m
        if n<n_star: Q*= (1+1/(3*ms[n]))
print("  max E_n over corridor times : %.6f"%mE_corr)
print("  max E_n over all orbit times: %.6f  (seed %d)"%(mE_all,argall))

print("\n=== 5. Does (U)'s stopping consequence already bound occupation? ===")
print("  claim: for n>=1, m_n = 1 and 2^c <= m_0  =>  n NOT in corridor")
c=1; viol=0; worstgap=0; tot=0
for m in range(3,60001,2):
    ms,ds=orbit(m); S=Sq(ds); n_star=len(ms)-1
    if m < 2**c: continue
    tot+=1
    Oc=sum(1 for n in range(n_star+1) if 2**S[n]<=(2**c)*3**n)
    # every corridor time must be < n_star
    mx=max(n for n in range(n_star+1) if 2**S[n]<=(2**c)*3**n)
    if mx>=n_star: viol+=1
    if Oc>n_star: viol+=1
    worstgap=max(worstgap,Oc-0)
print("  seeds tested %d ; violations of  O_c <= n*  : %d"%(tot,viol))
print("  => occupation is contained in [0, n*), so a stopping bound n* = O(log m0) gives EOC directly.")
