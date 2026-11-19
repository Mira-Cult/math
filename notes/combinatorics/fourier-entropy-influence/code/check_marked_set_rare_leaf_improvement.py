#!/usr/bin/env python3
"""Exact checks for the sharp-C4 arbitrary-marked-set rare-point theorem.

Run next to check_marked_set_closure.py in the canonical code directory.
The fallback filename supports the original author draft without changing
the mathematical implementation. Python standard library only.
"""

from fractions import Fraction as Q
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations, product
from math import comb
from pathlib import Path


paths = [Path(__file__).with_name(name) for name in
         ('check_marked_set_closure.py', 'check_two_point_closure.py')]
source = next(path for path in paths if path.exists())
spec = spec_from_file_location('marked_set_checker', source)
core = module_from_spec(spec)
spec.loader.exec_module(core)
LF = core.LogForm


def shifted_polynomial(coefficients, shift):
    """Coefficients of p(t+shift), in increasing powers of t."""
    out = [Q(0)] * len(coefficients)
    for degree, coefficient in enumerate(coefficients):
        for k in range(degree + 1):
            out[k] += coefficient * comb(degree, k) * shift ** (degree - k)
    return out


def check_universal_constants():
    # Nonnegative coefficients prove positivity at every nonnegative t;
    # these are exact polynomial identities, not sampling in q.
    assert shifted_polynomial([96, -45, 6], 4) == [12, 3, 6]
    assert shifted_polynomial([-132, 100, 8], 9) == [1416, 244, 8]
    for q in range(4, 9):
        assert -4 * q * q + 60 * q - 64 >= 28 * q - 64 > 0
    assert 9 ** 3 < 2 * 8 ** 3  # logarithmic increment is <1/3
    assert core.LN2[0] > Q(2, 3)
    assert Q(1, 20) + Q(4, 5) == Q(17, 20) < 1
    # Exact convex endpoint checks for the two exceptional q ranges.
    for aa, kk in product((0, 1), (Q(-1), Q(0))):
        assert 2 * abs(kk + 4 * aa) <= 8 < 12
    q3_max = Q(0)
    for av, kk, aa, bb in product((Q(4), Q(11)), (Q(-1), Q(0)),
                                  range(3), range(2)):
        if aa + bb > 2:
            continue
        score = abs(8 * bb - av) + 2 * abs(kk + 4 * aa - 4 * bb)
        assert score <= 27 < 28
        q3_max = max(q3_max, score)
    assert q3_max == 27
    print('PASS universal coefficient polynomials, logarithmic increment, '
          'q=2 and q=3 convex endpoints; exact rational arithmetic')


def rare_base(n):
    values = [1] * (1 << n)
    values[0] = -1
    return core.base_statistics(values)


def certify_rare_marked_leaf(base, marks):
    assert marks[0] == 0
    stats = core.mark_statistics(base, marks, Q(4))
    n, q, delta = stats['n'], len(marks), stats['delta']
    ordinary = marks[1:]
    aa = sum(x.bit_count() == 1 for x in ordinary)
    bb = sum((x ^ y).bit_count() == 1 for x, y in combinations(ordinary, 2))
    ell = LF.log((1 << (n - 1)) - 1)
    expected_k = delta * (q - 1) * (q - 4) * ell
    expected_p = (q - 2) * (2 - q * delta) * ell
    av = 4 * (q - 2) * (n - ell) + 2 * q * (q - 2) * delta * ell
    assert stats['K'] == expected_k and stats['P'] == expected_p
    assert stats['E'] == bb - aa
    assert stats['T'] == (q - 2) * n - 2 * bb
    assert stats['U'] == 8 * bb - av
    assert stats['V'] == expected_k + 4 * aa - 4 * bb
    assert av.interval()[0] >= 4 * (q - 2)
    assert av.interval()[1] <= (q - 2) * (q + 8)
    assert stats['U'].max_abs() + 2 * stats['V'].max_abs() <= Q(4, 5) * (4 * q * q - 1)
    assert stats['margin'].interval()[0] > delta
    core.invariant(stats)
    return stats


def check_leaf_marks():
    cases = 0
    for n in (2, 3, 4):
        base = rare_base(n)
        size = 1 << n
        for q in range(2, size + 1):
            for ordinary in combinations(range(1, size), q - 1):
                certify_rare_marked_leaf(base, (0,) + ordinary)
                cases += 1
    assert cases == 7 + 127 + 32767
    for n in (5, 6, 8):
        base = rare_base(n)
        size = 1 << n
        for q in sorted({2, 3, 4, 5, 8, 9, 16, size // 2, size}):
            certify_rare_marked_leaf(base, tuple(range(q)))
            cases += 1
    print(f'PASS exact rare-leaf formulas and C4 invariant: {cases} marked sets; '
          'all sets containing the exception for n=2,3,4; selected n=5,6,8 through q=256')


def check_recursive_nodes():
    count = 0
    for q in (2, 3, 4, 5, 8):
        n = max(2, (q - 1).bit_length())
        m = 2 + (q - 1).bit_length()
        base = rare_base(n)
        children = [certify_rare_marked_leaf(base, tuple(range(q))) for _ in range(m)]
        parent = core.product_node(children, Q(4))
        count += 1
        if q in (3, 4):
            # One non-leaf child and three leaf children; all q projected
            # marks remain distinct and the maximum dimension is fourteen.
            core.product_node([parent] + children[:m - 1], Q(4))
            count += 1
    print(f'PASS C4 recursive nodes: {count}; q=2,3,4,5,8; '
          f'maximum N={core.COUNTS["maximum_n"]}; includes depth two for q=3,4')


def main():
    check_universal_constants()
    check_leaf_marks()
    check_recursive_nodes()
    print('All logarithmic comparisons use certified rational atanh bounds; '
          'Fourier, boundary-edge, score, and polynomial identities are exact.')


if __name__ == '__main__':
    main()
