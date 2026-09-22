from functools import lru_cache
import sys
sys.setrecursionlimit(100000)
# --- literal mirror of the Lean definitions ---
@lru_cache(maxsize=None)
def oscS(c,n):
    if n==0: return 0
    p=oscS(c,n-1)
    return p + (2 if 2**p <= (2**c)*3**(n-1) else 1)
def oscD(c,n):
    p=oscS(c,n); return 2 if 2**p <= (2**c)*3**n else 1
def InC(c,n): return 2**oscS(c,n) <= (2**c)*3**n
def reentries(c,N): return [n for n in range(N) if (not InC(c,n)) and InC(c,n+1)]
def exitTime(c,i):
    n=0 if i==0 else exitTime(c,i-1)+1
    while InC(c,n): n+=1
    return n

print("oscD 1, n<30 :", ''.join(str(oscD(1,n)) for n in range(30)))
print("InC  1, n<30 :", ''.join('1' if InC(1,n) else '0' for n in range(30)))
print("exitTime 1   :", [exitTime(1,i) for i in range(8)])
print("reentries(1,N).card for N=10..60:", [len(reentries(1,10*k+10)) for k in range(6)])
for c in (0,1,2):
    print("  |reentries(%d,60)| = %d"%(c,len(reentries(c,60))))

print("\n=== CONVENTION AUDIT: exit-indexed vs re-entry-indexed counting ===")
c=1;N=60
ex=[n for n in range(N) if (not InC(c,n)) and InC(c,n+1)]      # Lean: indexed by EXIT time n
re=[n for n in range(1,N) if (not InC(c,n-1)) and InC(c,n)]    # earlier python: indexed by RE-ENTRY time n
print("  Lean  reentries(c,%d): indexed by exit time, card=%d, max=%d"%(N,len(ex),max(ex)))
print("  py    re-entry times < %d          : card=%d, max=%d"%(N,len(re),max(re)))
print("  shifted agreement: {n+1 : n in Lean set} == py set restricted to <%d ? %s"%(N,
      sorted(n+1 for n in ex if n+1<N)==sorted(re)))
print("  => the two differ only by the index convention (exit n <-> re-entry n+1); Lean's set")
print("     counts exits n<N, so it may include one whose re-entry is at N itself. Both are")
print("     lower bounds on the number of episodes after the first, which is all that is used.")

print("\n=== episode count vs re-entry count (the 'initial episode is not a return' point) ===")
for N in (20,40,60):
    inC=[InC(c,n) for n in range(N+1)]
    runs=0;prev=False
    for n in range(N+1):
        if inC[n] and not prev: runs+=1
        prev=inC[n]
    print("  N=%2d : maximal in-corridor runs in [0,N] = %d ; re-entries (exit-indexed) < N = %d"
          %(N,runs,len([n for n in range(N) if (not InC(c,n)) and InC(c,n+1)])))
print("  runs = re-entries + 1 (the initial episode at n=0), as expected.")
