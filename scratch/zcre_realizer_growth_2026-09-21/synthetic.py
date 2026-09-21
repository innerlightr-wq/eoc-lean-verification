import math, random
alpha = math.log2(3)

def s_word(d, N): return sum(d[:N])
def q_word(d, N):
    q = 0
    for j in range(N):
        q = 3*q + 2**s_word(d, j)
    return q
def least_realizer(d, N):
    S = s_word(d, N); qN = q_word(d, N); mod = 2**(S+1)
    target = (2**S - qN) % mod
    inv3N = pow(pow(3, N, mod), -1, mod)
    return (target * inv3N) % mod

def floorA(n): return math.floor(alpha*n)

def gen_zero_corridor(length, strategy, seed=0):
    rng = random.Random(seed)
    d = []
    S = 0
    for n in range(1, length+1):
        cap = floorA(n) - S          # max digit keeping S_n <= floor(alpha n)
        if cap < 1:
            raise RuntimeError("infeasible")
        if strategy == "min":
            dn = 1
        elif strategy == "max":
            dn = cap
        elif strategy == "rand":
            dn = rng.randint(1, cap)
        elif strategy == "alt":
            dn = 1 if (n % 2 == 0) else cap
        d.append(dn)
        S += dn
    return d

print("=== Synthetic zero-corridor words: realizer growth ===")
for strategy in ["min", "max", "rand", "alt"]:
    for seed in range(3):
        d = gen_zero_corridor(40, strategy, seed=seed)
        rs = [least_realizer(d, N) for N in range(1, 41)]
        Delta = [floorA(N) - s_word(d,N) for N in range(1,41)]
        print(f"strategy={strategy:5s} seed={seed}  Delta_40={Delta[-1]:4d}  "
              f"r_N (every 5th, N=5..40): {rs[4::5]}")
