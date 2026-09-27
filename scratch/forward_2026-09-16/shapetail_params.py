"""Exact integer audit of proposed unconditional ShapeTail schedules.

No floating point is used in the inequality test.  We test rho = 2^(-j/1000)
in the stronger denominator-cleared form after restricting to j divisible by 1000:

  j * (3/2)^(j/2) * 2^sigma * 2^(j/1000)
    <= 3^T * choose(sigma-1,j-1).
"""
from math import comb


def barrier(j: int) -> int:
    # floor(j log_2 3), determined exactly by comparing 3^j and powers of 2.
    x = 3**j
    return x.bit_length() - 1


def check(j: int):
    assert j % 1000 == 0
    sigma = barrier(j)
    T = 31 * j // 100
    K = j // 25
    budget_ok = K + T + sigma // 12 <= j // 2
    # Clear (3/2)^(j/2) and rho = 2^(-j/1000).
    lhs = j * 3 ** (j // 2) * 2 ** (sigma + j // 1000)
    rhs = 2 ** (j // 2) * 3**T * comb(sigma - 1, j - 1)
    return sigma, T, K, budget_ok, lhs <= rhs, rhs.bit_length() - lhs.bit_length()


for j in range(1000, 20001, 1000):
    print(j, check(j))
