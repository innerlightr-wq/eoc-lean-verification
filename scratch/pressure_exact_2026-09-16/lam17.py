"""lambda = 17, J = 1600, t = J/6: exact global pressure and telescoped window maxima, for the Lean observable
(eligible dark, d = 1/108 and 1/54) and for the old surrogate (all own odd choices, Tao-black eta = 1/54)."""
from pexact import Instance, log2ratio, below
j, t, lam = 1600, 1600 // 6, 17
for label, D, obs in (("surrogate black eta=1/54", 54, 'black'), ("Lean odd d=1/54", 54, 'odd'), ("Lean odd d=1/108", 108, 'odd')):
    I = Instance(j, t, lam=lam, D=D, mode='auto', obs=obs)
    Z3, Z1 = I.moment(3), I.moment(1)
    w, _ = I.blocks(3)
    out = []
    for K in (16, 24, 32, 64, 128):
        best, arg = max((sum(w[a:a + K]) / (2 * K), a) for a in range(len(w) - K + 1))
        out.append(f"K={K}: {best:.4f}@r0={arg}")
    print(f"{label:26s} P={log2ratio(Z3, Z1)/j:.5f} certified<0.17={below(Z3, Z1, j, 17, 100)}  " + "  ".join(out))
