from math import log2
A=log2(3)

# ---- the oscillating word: digit 2 when in corridor, digit 1 when out ----
def word(c,N):
    d=[];S=[0]
    for n in range(N):
        inC = 2**S[n] <= (2**c)*3**n
        dn = 2 if inC else 1
        d.append(dn); S.append(S[n]+dn)
    return d,S

for c in (0,1,2):
    d,S=word(c,40)
    inC=[2**S[n]<=(2**c)*3**n for n in range(41)]
    re=[n for n in range(1,40) if (not inC[n-1]) and inC[n]]
    print("c=%d word[0:30]=%s"%(c,''.join(map(str,d[:30]))))
    print("      in-corridor[0:30]=%s   re-entries<40: %s"%(''.join('1' if b else '0' for b in inC[:30]), re))
    # structural checks
    assert all(inC[n+1] for n in range(40) if not inC[n]), "immediate re-entry fails"
    assert not all(inC[n] and inC[n+1] and inC[n+2] for n in range(1,38)), "run bound"
    runs=[]; k=0
    for n in range(41):
        if inC[n]: k+=1
        else:
            if k: runs.append(k)
            k=0
    print("      episode lengths (in-corridor runs): %s  ; max run after first exit: %d"%(runs, max(runs[1:]) if len(runs)>1 else 0))

print("\n=== re-entry count grows linearly in N (c=1) ===")
c=1
for N in (30,60,120,240,480,960):
    d,S=word(c,N)
    inC=[2**S[n]<=(2**c)*3**n for n in range(N+1)]
    re=sum(1 for n in range(1,N) if (not inC[n-1]) and inC[n])
    print("   N=%4d  re-entries=%4d   ratio N/re=%.3f"%(N,re,N/re))

# ---- realization bridge: leastRealizer of the prefix ----
def leastRealizer(d,N):
    S=sum(d[:N]); q=0
    for i in range(N): q=3*q+2**sum(d[:i])   # q_{i+1}=3q_i+2^{s_i}
    M=2**(S+1); tgt=(2**S - q)%M
    x=(tgt*pow(pow(3,-1,M),N,M))%M
    return x,S,q
print("\n=== finite prefixes realized by positive odd seeds (c=1) ===")
c=1
print("  %4s %5s %6s %24s %s"%("N","re","S_N","leastRealizer r","odd? verified?"))
for N in (10,20,30,40,50,60):
    d,S_=word(c,N)
    inC=[2**S_[n]<=(2**c)*3**n for n in range(N+1)]
    re=sum(1 for n in range(1,N) if (not inC[n-1]) and inC[n])
    x,S,q=leastRealizer(d,N)
    # verify by running the real accelerated orbit
    ok=True; m=x
    for i in range(N):
        y=3*m+1; dd=0
        while y%2==0: y//=2; dd+=1
        if dd!=d[i]: ok=False; break
        m=y
    print("  %4d %5d %6d %24d %s"%(N,re,S,x,("odd " if x%2==1 else "EVEN")+("OK" if ok else "MISMATCH")))
