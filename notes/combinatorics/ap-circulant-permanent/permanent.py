"""Division-free permanents of additive matrices plus a constant staircase.

See README.md for the invariant and arithmetic versus bit-complexity bounds.
Only the Python standard library is needed. Inputs may be integers, Fractions,
or commutative-ring objects supporting arithmetic with Python integer scalars.
"""

from collections import defaultdict
from typing import Any, Sequence


def permanent_staircase(u: Sequence[Any], v: Sequence[Any], t: Any) -> Any:
    """Return per(M), M[i,j] = u[i] + v[j] + t * (j < i).

    The mathematical algorithm uses O(n^5) ring operations and O(n^4)
    stored ring elements. The sparse dictionary implementation is convenient;
    dense four-counter arrays give deterministic indexed state access.
    """
    n = len(u)
    if len(v) != n:
        raise ValueError("u and v must have equal lengths")
    # h = open T columns; k = matched T edges; r,c = U rows, U columns.
    states = {(0, 0, 0, 0): 1}
    for i in range(n):
        row = defaultdict(lambda: 0)
        for (h, k, r, c), weight in states.items():
            if h:
                row[h - 1, k + 1, r, c] += weight * t * h
            row[h, k, r + 1, c] += weight * u[i]
            row[h, k, r, c] += weight

        remaining = n - i - 1
        column = defaultdict(lambda: 0)

        def add(h, k, r, c, weight):
            if h <= remaining and abs(r - c) <= remaining:
                column[h, k, r, c] += weight

        for (h, k, r, c), weight in row.items():
            add(h + 1, k, r, c, weight)
            add(h, k, r, c + 1, weight)
            add(h, k, r, c, weight * v[i])
        states = column

    factorials = [1]
    for i in range(1, n + 1):
        factorials.append(factorials[-1] * i)
    answer = 0
    for (h, k, r, c), weight in states.items():
        if h == 0 and r == c and k + r <= n:
            answer += weight * factorials[r] * factorials[n - k - r]
    return answer


def permanent_ap_circulant(n: int, a: Any, b: Any) -> Any:
    """Return per(C), C[i,j] = a + b * ((j-i) mod n); per(empty) = 1."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    return permanent_staircase(
        [a - i * b for i in range(n)],
        [j * b for j in range(n)],
        n * b,
    )


if __name__ == "__main__":
    from argparse import ArgumentParser
    from fractions import Fraction

    parser = ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("a", type=Fraction, help="first entry, e.g. 1 or 2/3")
    parser.add_argument("b", type=Fraction, help="common difference")
    args = parser.parse_args()
    print(permanent_ap_circulant(args.n, args.a, args.b))
