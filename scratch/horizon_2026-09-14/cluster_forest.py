"""Part XXII (secondary): cluster constant.  Survivors (exit > N, mu < X) and their windows
{mu, T mu, ..., T^(N-1) mu} form a forest; clusters = components; each component has one terminal
node (its furthest point), so  #clusters = #survivors whose endpoint T^(N-1) mu is not an interior
(position < N-1) point of another survivor's window  ("terminal survivors").
Measured: P(terminal), number of 'extenders' per survivor (survivors whose window contains
T^(N-1) mu at an earlier position), split into on-orbit extenders (y = T^t mu) and sibling-merge
extenders; and the renewal law P(no extender) vs 1/(1 + E[#extenders])."""
import struct, sys
from collections import Counter, defaultdict
fn, HI, N = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
def T(m):
    x = 3 * m + 1
    while not x & 1: x >>= 1
    return x
surv = []
data = open(fn, "rb").read()
for off in range(0, len(data), 12):
    mu, e = struct.unpack_from("<QI", data, off)
    if e > N and mu < 2 ** HI: surv.append(mu)
pos = defaultdict(list)   # value -> [(seed index, position)]
ends = []
for i, mu in enumerate(surv):
    m = mu
    for t in range(N):
        pos[m].append((i, t))
        if t < N - 1: m = T(m)
    ends.append(m)
idx = {mu: i for i, mu in enumerate(surv)}
term = 0; ext_on = []; ext_sib = []
for i, mu in enumerate(surv):
    z = ends[i]
    exts = [(j, t) for (j, t) in pos[z] if j != i and t < N - 1]
    # classify: on-orbit if the extender's start is on mu's own window (y = T^t mu) i.e. y's window
    # contains mu's window start?  y = T^s mu  <=>  surv[j] appears in mu's window at position s.
    won = 0; wsib = 0
    for (j, t) in exts:
        if any(jj == i for (jj, s) in pos[surv[j]]):   # surv[j] is a value on mu's window
            won += 1
        else:
            wsib += 1
    ext_on.append(won); ext_sib.append(wsib)
    if not exts: term += 1
S = len(surv)
Eon = sum(ext_on) / S; Esib = sum(ext_sib) / S
p0on = sum(1 for v in ext_on if v == 0) / S
print(f"N={N} X=2^{HI}: survivors {S}; terminal fraction {term/S:.4f}  => survivors/clusters = {S/term:.3f}")
print(f"  E[#on-orbit extenders] = {Eon:.4f}   E[#sibling extenders] = {Esib:.4f}   total {Eon+Esib:.4f}")
print(f"  P(no on-orbit extender) = {p0on:.4f}   vs renewal 1/(1+E_on) = {1/(1+Eon):.4f}")
print(f"  P(terminal) = {term/S:.4f}   vs renewal 1/(1+E_on+E_sib) = {1/(1+Eon+Esib):.4f}")
print("  distribution of total extenders:", sorted(Counter(a + b for a, b in zip(ext_on, ext_sib)).items())[:8])
