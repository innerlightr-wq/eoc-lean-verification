"""Exact integer certification (as in logwindows_2026-09-16/certify.py) of the worst sampled shifts, K = ceil(2 log2 j)."""
import json, sys
sys.path.insert(0, '../logwindows_2026-09-16')
from multiprocessing import Pool
from certify import certify
if __name__ == '__main__':
    rows = [json.loads(l) for l in open('shifts.jsonl')]
    specs = []
    for j in (400, 800, 1600):
        rs = sorted((r for r in rows if r['j'] == j and r['kind'] == 'lam1' and r['A'] == 2), key=lambda r: -r['max_rate'])[:3]
        specs += [(j, r['t'], 1) for r in rs]
    with Pool(6) as p:
        for r in p.imap_unordered(certify, specs): print(json.dumps(r))
