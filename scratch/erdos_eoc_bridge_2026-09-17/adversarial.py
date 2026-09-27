"""Parts XXIII / XLIV: low-complexity, exponentially sparse targets that the orbit 2^n hits EVERY time.
T_{D,N} := {2^n mod 3^D : 0 <= n <= N}  (one fixed, n-independent clopen set).
Haar measure (N+1)/3^D; minimal DFA size (reading ternary digits low-first, and high-first) computed exactly by
Myhill-Nerode on the finite language (states = distinct residual languages, per level, plus the dead state).
Also the 'moving' version E_n = ball(2^n, 3^{-D}) (one cylinder, D+1 states) trivially hit for every n."""
def words(D, N):
    out=set(); x=1; m=3**D
    for n in range(N+1):
        v=x; w=[]
        for _ in range(D): w.append(v%3); v//=3
        out.add(tuple(w)); x=x*2%m
    return out
def min_dfa_states(L, D):
    # residuals at level k: map prefix -> frozenset of suffixes; count distinct nonempty residuals per level
    total=0
    for k in range(D+1):
        res={}
        for w in L:
            res.setdefault(w[:k], set()).add(w[k:])
        total+=len({frozenset(s) for s in res.values()})
    return total+1  # + dead state
import math
print(" D     N    |T|/3^D        DFA(low-first)  DFA(high-first)   log3(3^D/(N+1))")
for D in (8, 10, 12, 14):
    for N in (D, D*D, D**3):
        if N+1 >= 2*3**(D-1): continue
        L=words(D,N)
        lo=min_dfa_states(L,D); hi=min_dfa_states({w[::-1] for w in L},D)
        print(f"{D:2d} {N:6d}  {(N+1)/3**D:.3e}   {lo:8d}        {hi:8d}          {math.log(3**D/(N+1),3):.2f}")
