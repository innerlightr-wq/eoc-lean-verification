"""Anti-tautology: does the bridge g <= ceil(H) have content, or does it hold for any H?
Corrupt H in three ways and count how often the assertion fires."""
import math, sys, importlib.util
spec = importlib.util.spec_from_file_location("tr", "scratch/transport_regeneration.py")
tr = importlib.util.module_from_spec(spec); spec.loader.exec_module(tr)

variants = {"true H = F + M": lambda F, M: F + M,
            "M -> -1":        lambda F, M: F - 1,
            "F -> F/2":       lambda F, M: F/2 + M,
            "H -> log2(1+H)": lambda F, M: math.log2(1 + F + M)}
fired = {k: 0 for k in variants}; total = 0
for m0 in range(3, 6001, 2):
    ds, ms, S, rows, M2, inv3 = tr.analyse(m0, 40)
    for R in rows:
        if not R['validM'] or R['g'] is None: continue
        total += 1
        for k, f in variants.items():
            if not (R['g'] <= math.ceil(f(R['F'], R['M']) - 1e-12)): fired[k] += 1
print(f"steps tested: {total}")
for k in variants: print(f"  {k:18s} violations: {fired[k]:6d}  ({100*fired[k]/total:5.2f}%)")
