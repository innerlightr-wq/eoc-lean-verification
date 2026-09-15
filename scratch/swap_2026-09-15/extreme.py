import glob, re, math
from collections import defaultdict
rows = defaultdict(list)
for f in glob.glob('deep_J*_t*_*.txt'):
    J = int(re.search(r'J(\d+)', f).group(1)); t = int(re.search(r'_t(\d+)', f).group(1))
    for line in open(f):
        if line.startswith('h='):
            d = dict(re.findall(r'(\w+)=([-\d.e+]+)', line))
            rows[(J, t)].append((float(d['swap']), float(d['blk2']), float(d['phi'])))
print(" j0   t   n     swap: mean  std  s=std*sqrt(j0)  min   | extreme-value prediction over 2^t freqs | blk2 mean std min")
for (J, t) in sorted(rows):
    R = rows[(J, t)]; n = len(R)
    for idx, name in ((0, 'swap'), (1, 'blk2')):
        rates = [-math.log2(r[idx]) / J for r in R]
        mu = sum(rates) / n; sd = math.sqrt(sum((x - mu) ** 2 for x in rates) / (n - 1)); mn = min(rates)
        pred = mu - sd * math.sqrt(2 * math.log(2 ** t))
        if idx == 0: line = f" {J:3d}  {t:2d}  {n:4d}   {mu:.4f} {sd:.4f}  {sd*math.sqrt(J):.3f}   {mn:.4f}  | pred min over 2^{t}: {pred:.4f} (sample-size pred {mu - sd*math.sqrt(2*math.log(n)):.4f})"
        else: line += f" | {mu:.4f} {sd:.4f} {mn:.4f} pred {pred:.4f}"
    print(line)
