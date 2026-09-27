"""loader for the sharded press_<J>_<tag>.json files."""
import json, os

DIR = os.path.dirname(os.path.abspath(__file__))
THETA_MAX = 0.137


def load(J, tags=("a", "b", "c")):
    """returns (meta, {lam(int): rec}) with rec = {'pre','nblack','depth','P':{K:{...}}}"""
    meta, envs = None, {}
    for t in tags:
        p = os.path.join(DIR, f"press_{J}_{t}.json")
        if not os.path.exists(p):
            continue
        d = json.load(open(p))
        if meta is None:
            meta = {k: v for k, v in d.items() if k != "env"}
        for lam, rec in d["env"].items():
            envs[int(lam)] = rec
    return meta, envs


def series(rec, K):
    """(j0, [P_j]) for the given K, or None."""
    s = rec["P"].get(str(K))
    if s is None:
        return None
    return s["j0"], s["P"]
