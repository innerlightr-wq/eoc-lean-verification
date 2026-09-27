"""Part III: exact upper-tail rates of N_odd vs J, fits (a + b/J, a + b/sqrt J, J >= 400), and a Poisson benchmark
with the exact mean: per-step bits  mu h(q/mu)/(2 ln 2),  h(x) = x ln x - x + 1,  mu = E[N_odd]/R."""
import re, math
QS = (0.05, 0.06, 0.075, 0.10)
for env in ("true", "random"):
    rows = []
    for J in (100, 200, 400, 800, 1200):
        try: s = open(f"ODD_{env}_{J}.txt").read()
        except FileNotFoundError: continue
        mu = float(re.search(r"= ([0-9.]+) R;", s).group(1))
        rt = {float(a): float(b) for a, b in re.findall(r"q=([0-9.]+): 2\^-[0-9.]+ \(rate ([0-9.]+)\)", s.split("(2)")[1].split("\n")[0])}
        rows.append((J, mu, rt))
    print(f"env={env}:  J   mean/R  | exact rate q=0.05 0.06 0.075 0.10 | Poisson-benchmark q=0.05 0.06 0.075 0.10")
    for J, mu, rt in rows:
        pb = [(mu * ((q / mu) * math.log(q / mu) - q / mu + 1)) / (2 * math.log(2)) if q > mu else 0 for q in QS]
        print(f"   {J:5d}  {mu:.4f} | " + " ".join(f"{rt.get(q, float('nan')):.4f}" for q in QS) + " | " + " ".join(f"{x:.4f}" for x in pb))
    for q in (0.075, 0.10):
        pts = [(J, rt[q]) for J, mu, rt in rows if J >= 400]
        for name, f in (("a+b/J", lambda J: 1 / J), ("a+b/sqrtJ", lambda J: 1 / math.sqrt(J))):
            n = len(pts); xs = [f(J) for J, _ in pts]; ys = [y for _, y in pts]
            mx = sum(xs) / n; my = sum(ys) / n
            bb = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs); aa = my - bb * mx
            print(f"   fit q={q} {name}: limit a = {aa:.4f}, b = {bb:.3f}")
