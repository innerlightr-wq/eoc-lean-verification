"""Aksenov-style exploratory plots, rendered as SVG with the standard library only.

Gate 12. Deliberately no matplotlib/numpy: neither is installed here, and adding a
plotting stack to a Lean repository for five exploratory scatters is not a
justified dependency. SVG is text, so the output is diffable and reviewable in
git, which a PNG is not.

A resemblance between these plots and the paper's Mathlib plots says something
about dependency graphs in general. It says NOTHING about whether EOC's
mathematics is correct or its research directions are sound.
"""
from __future__ import annotations

import json
import statistics
from pathlib import Path

W, H, PAD = 560, 380, 58


def _svg(points, xlabel, ylabel, title, note="", fit=None):
    if not points:
        return "<svg xmlns='http://www.w3.org/2000/svg'/>"
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    x0, x1 = min(xs), max(xs)
    y0, y1 = min(ys), max(ys)
    x1 = x1 + 1e-9 if x1 == x0 else x1
    y1 = y1 + 1e-9 if y1 == y0 else y1

    def sx(v):
        return PAD + (v - x0) / (x1 - x0) * (W - 2 * PAD)

    def sy(v):
        return H - PAD - (v - y0) / (y1 - y0) * (H - 2 * PAD)

    out = [f"<svg xmlns='http://www.w3.org/2000/svg' width='{W}' height='{H}' "
           f"viewBox='0 0 {W} {H}' font-family='system-ui,sans-serif' font-size='11'>",
           f"<rect width='{W}' height='{H}' fill='#fff'/>",
           f"<text x='{W/2}' y='20' text-anchor='middle' font-size='13' "
           f"font-weight='600'>{title}</text>"]
    if note:
        out.append(f"<text x='{W/2}' y='35' text-anchor='middle' fill='#666'>{note}</text>")
    out.append(f"<line x1='{PAD}' y1='{H-PAD}' x2='{W-PAD}' y2='{H-PAD}' stroke='#333'/>")
    out.append(f"<line x1='{PAD}' y1='{PAD}' x2='{PAD}' y2='{H-PAD}' stroke='#333'/>")
    for frac in (0.0, 0.5, 1.0):
        xv, yv = x0 + frac * (x1 - x0), y0 + frac * (y1 - y0)
        out.append(f"<text x='{sx(xv):.1f}' y='{H-PAD+16}' text-anchor='middle' "
                   f"fill='#444'>{xv:.4g}</text>")
        out.append(f"<text x='{PAD-6}' y='{sy(yv):.1f}' text-anchor='end' "
                   f"fill='#444'>{yv:.4g}</text>")
    out.append(f"<text x='{W/2}' y='{H-12}' text-anchor='middle' fill='#222'>{xlabel}</text>")
    out.append(f"<text x='14' y='{H/2}' text-anchor='middle' fill='#222' "
               f"transform='rotate(-90 14 {H/2})'>{ylabel}</text>")
    for x, y in points:
        out.append(f"<circle cx='{sx(x):.1f}' cy='{sy(y):.1f}' r='1.9' "
                   f"fill='#2b6cb0' fill-opacity='0.35'/>")
    if fit:
        m, b = fit
        out.append(f"<line x1='{sx(x0):.1f}' y1='{sy(m*x0+b):.1f}' "
                   f"x2='{sx(x1):.1f}' y2='{sy(m*x1+b):.1f}' "
                   f"stroke='#c53030' stroke-width='1.5' stroke-dasharray='5,3'/>")
    out.append("</svg>")
    return "\n".join(out)


def _ols(points):
    """Least-squares slope/intercept, or None if the sample cannot support one."""
    n = len(points)
    if n < 30:
        return None, {"refused": "fewer than 30 points"}
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    if len(set(xs)) < 4:
        return None, {"refused": "fewer than 4 distinct x values"}
    mx, my = statistics.fmean(xs), statistics.fmean(ys)
    sxx = sum((x - mx) ** 2 for x in xs)
    if sxx == 0:
        return None, {"refused": "zero x variance"}
    m = sum((x - mx) * (y - my) for x, y in points) / sxx
    b = my - m * mx
    ss_tot = sum((y - my) ** 2 for y in ys)
    ss_res = sum((y - (m * x + b)) ** 2 for x, y in points)
    r2 = 1 - ss_res / ss_tot if ss_tot else 0.0
    return (m, b), {"slope": round(m, 4), "intercept": round(b, 4),
                    "r2": round(r2, 4), "n": n}


def generate(graph_path: Path, outdir: Path) -> dict:
    g = json.loads(graph_path.read_text(encoding="utf-8"))
    d = [x for x in g["declarations"].values()
         if not x["generated"] and x["wrapped_tokens_approx"] > 0]
    outdir.mkdir(parents=True, exist_ok=True)
    report: dict = {"sample": {"human_written_with_source": len(d),
                               "total_eoc": g["totals"]["eoc_declarations"],
                               "excluded_generated": g["totals"]["eoc_declarations"]
                               - g["totals"]["eoc_declarations_human"],
                               "excluded_no_source_range":
                                   g["totals"]["eoc_declarations_human"] - len(d)},
                    "figures": {}}

    specs = [
        ("01_log2unwrapped_vs_depth_viewB",
         [(x["view_B"]["depth"], x["view_B"]["unwrapped"]["log2"]) for x in d],
         "dependency depth (View B, EOC-relative)", "log2(unwrapped)",
         "log2(unwrapped) vs depth — EOC-relative"),
        ("02_log2unwrapped_vs_depth_viewA",
         [(x["view_A"]["depth"], x["view_A"]["unwrapped"]["log2"]) for x in d],
         "dependency depth (View A, into Mathlib)", "log2(unwrapped)",
         "log2(unwrapped) vs depth — full formal"),
        ("03_wrapped_vs_depth_viewB",
         [(x["view_B"]["depth"], x["wrapped_tokens_approx"]) for x in d],
         "dependency depth (View B)", "wrapped tokens (approx)",
         "wrapped length vs depth — EOC-relative"),
        ("04_log2unwrapped_vs_wrapped_viewB",
         [(x["wrapped_tokens_approx"], x["view_B"]["unwrapped"]["log2"]) for x in d],
         "wrapped tokens (approx)", "log2(unwrapped), View B",
         "log2(unwrapped) vs wrapped length — EOC-relative"),
        ("05_centrality_vs_compression",
         [(x["view_B"]["unwrapped"]["log2"] / x["wrapped_tokens_approx"],
           x.get("pagerank_viewB", 0.0)) for x in d],
         "compression (bits of unwrapped per token)", "J0-biased PageRank (View B)",
         "centrality vs compression"),
    ]
    for name, pts, xl, yl, title in specs:
        fit, stats = _ols(pts)
        note = (f"n={len(pts)}; slope {stats['slope']} (R²={stats['r2']})"
                if fit else f"n={len(pts)}; no slope reported — {stats['refused']}")
        (outdir / f"{name}.svg").write_text(
            _svg(pts, xl, yl, title, note, fit), encoding="utf-8")
        report["figures"][name] = stats

    # binned medians — more honest than a slope at this sample size
    bins: dict[int, list[int]] = {}
    for x in d:
        bins.setdefault(x["view_B"]["depth"], []).append(x["view_B"]["unwrapped"]["log2"])
    report["median_log2unwrapped_by_depth_viewB"] = {
        str(k): {"n": len(v), "median": statistics.median(v)} for k, v in sorted(bins.items())}
    binsA: dict[int, list[int]] = {}
    for x in d:
        binsA.setdefault(x["view_A"]["depth"] // 10 * 10, []).append(x["view_A"]["unwrapped"]["log2"])
    report["median_log2unwrapped_by_depth_viewA_binned10"] = {
        str(k): {"n": len(v), "median": statistics.median(v)} for k, v in sorted(binsA.items())}

    # top historical/impact nodes, components kept separate (Gate 5)
    top = sorted(d, key=lambda x: -x.get("pagerank_viewB", 0.0))[:12]
    report["top_by_pagerank_components_separate"] = [{
        "name": x["name"],
        "pagerank_viewB": x.get("pagerank_viewB", 0.0),
        "rev_deps_eoc": len(x["rev_deps_eoc"]),
        "depth_viewB": x["view_B"]["depth"],
        "log2_unwrapped_viewB": x["view_B"]["unwrapped"]["log2"],
        "wrapped_tokens_approx": x["wrapped_tokens_approx"],
        "T0_viewB": x["T0_viewB"],
    } for x in top]
    (outdir / "plot_stats.json").write_text(
        json.dumps(report, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    return report
