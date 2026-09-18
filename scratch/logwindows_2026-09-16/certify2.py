"""Second certification batch (same exact test as certify.py): larger j, all required shift samples."""
import json, sys
from multiprocessing import Pool
from certify import certify
if __name__ == '__main__':
    specs = []
    for j in (3200, 6400):
        for t in (1, 7, j // 6, j, 5 * j):
            specs.append((j, t, 1))
        specs.append((j, j // 6, 17))
    for t in (1, 12800 // 6):
        specs.append((12800, t, 1))
    with Pool(3) as pool:
        for res in pool.imap_unordered(certify, specs):
            with open('certify2.jsonl', 'a') as fh: fh.write(json.dumps(res) + '\n')
    print('done', len(specs))
