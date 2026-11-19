#!/usr/bin/env python3
"""Exact certificates for forest_selector_interpolation.md.

Python standard library only. Default checks:
  * all 14 rational Bernstein coefficients;
  * every ordered eligible Boolean branch pair on 0,1,2,3 data bits;
  * exact bent-selector truth tables for m=1,2,3;
  * alternating first-hit lists for m=1,2 and k=1,...,6.

Eligible branches have power-of-two Walsh magnitudes and are either constant
or satisfy the exactly computed slack 4I-H>=2. This is a larger finite test
set than the forest hypotheses; no forest recognizer is being substituted.
Entropy comparisons use certified rational logarithm intervals. The printed
decimal diagnostics are not used in assertions. The universal inequalities
have analytic proofs in the manuscript, not finite-enumeration proofs.
"""

from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from math import comb


def walsh(values):
    out = list(values)
    step = 1
    while step < len(out):
        for block in range(0, len(out), 2 * step):
            for j in range(block, block + step):
                a, b = out[j], out[j + step]
                out[j], out[j + step] = a + b, a - b
        step *= 2
    return out


def log_interval(x, terms=50):
    """Enclose natural log x for 1<=x<=2 by its positive atanh series."""
    assert 1 <= x <= 2
    u = (x - 1) / (x + 1)
    power, square = u, u * u
    partial = Q(0)
    for j in range(terms):
        partial += power / (2 * j + 1)
        power *= square
    lower = 2 * partial
    upper = lower + 2 * power / ((2 * terms + 1) * (1 - square))
    return lower, upper


LN2_LO, LN2_HI = log_interval(Q(2))


@lru_cache(None)
def log2_integer_interval(value):
    assert value >= 1
    exponent = value.bit_length() - 1
    reduced = Q(value, 1 << exponent)
    if reduced == 1:
        return Q(exponent), Q(exponent)
    lo, hi = log_interval(reduced)
    return exponent + lo / LN2_HI, exponent + hi / LN2_LO


def entropy_interval(w):
    size = len(w)
    n = size.bit_length() - 1
    assert size == 1 << n
    assert sum(a * a for a in w) == size * size
    total_lo, total_hi = Q(0), Q(0)
    for magnitude, count in Counter(map(abs, w)).items():
        if not magnitude:
            continue
        p = Q(count * magnitude * magnitude, size * size)
        lo, hi = log2_integer_interval(magnitude)
        total_lo += p * lo
        total_hi += p * hi
    return 2 * n - 2 * total_hi, 2 * n - 2 * total_lo


def influence(w):
    return Q(sum(s.bit_count() * a * a for s, a in enumerate(w)), len(w) ** 2)


def is_power_two(value):
    return value > 0 and value & (value - 1) == 0


def poly_add(a, b):
    out = [Q(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    return out


def poly_scale(a, c):
    return [c * x for x in a]


def poly_mul(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def bernstein_coefficients(poly, left, right):
    degree = len(poly) - 1
    translated = [Q(0)] * (degree + 1)
    for i, value in enumerate(poly):
        for j in range(i + 1):
            translated[j] += value * comb(i, j) * left ** (i - j) * (right - left) ** j
    return [sum(translated[j] * Q(comb(k, j), comb(degree, j))
                for j in range(k + 1)) for k in range(degree + 1)]


def check_polynomial_certificate():
    assert Q(69, 100) < Q(56, 81) < LN2_LO <= LN2_HI < Q(25, 36) < Q(7, 10)
    assert 3 ** 12 > 2 ** 19
    w = [Q(0), Q(4), Q(-4)]
    square = [Q(1, 16), Q(-1, 2), Q(1)]
    p = poly_add([Q(5, 12), Q(-29, 12)], poly_scale(square, Q(-20, 7)))
    p = poly_add(p, poly_scale(w, Q(50, 69)))
    p = poly_add(p, poly_scale(poly_mul(w, w), Q(25, 207)))
    p = poly_add(p, poly_scale(poly_mul(poly_mul(w, w), w), Q(1, 6)))
    q = poly_add([Q(1, 2)], poly_scale(p, -1))
    assert q == [Q(11, 42), Q(-3691, 1932), Q(5540, 1449),
                 Q(-1408, 207), Q(6224, 207), Q(-32), Q(32, 3)]
    rows = [bernstein_coefficients(q, Q(0), Q(1, 4)),
            bernstein_coefficients(q, Q(1, 4), Q(1, 2))]
    expected = [[728640, 507180, 330040, 182436, 71368, 11130, 16065],
                [16065, 21000, 91108, 240732, 484264, 828900, 1274640]]
    for row, numerator in zip(rows, expected):
        assert [value * 2782080 for value in row] == numerator
        assert min(row) > 0
    lo, hi = log2_integer_interval(3)
    assert Q(7470, 1000) < 36 - 18 * hi <= 36 - 18 * lo < Q(7471, 1000)
    print('Rational polynomial certificate: all 14 coefficients positive.')
    print('Separated-amplitude constant: 7.470 < C_* < 7.471.')


def check_small_pairs():
    total_pairs = 0
    for n in range(4):
        size = 1 << n
        eligible = []
        for truth_mask in range(1 << size):
            truth = [1 if (truth_mask >> j) & 1 else -1 for j in range(size)]
            w = walsh(truth)
            if any(a and not is_power_two(abs(a)) for a in w):
                continue
            hlo, hhi = entropy_interval(w)
            assert hlo == hhi
            inf = influence(w)
            constant = inf == 0
            if constant or 4 * inf - hhi >= 2:
                eligible.append((w, hhi, inf, constant))
        checked = 0
        for wg, hg, ig, cg in eligible:
            for wh, hh, ih, ch in eligible:
                parent = [a + b for a, b in zip(wg, wh)] + [a - b for a, b in zip(wg, wh)]
                hlo, hhi = entropy_interval(parent)
                inf = influence(parent)
                control = Q(sum((a - b) ** 2 for a, b in zip(wg, wh)), 4 * size ** 2)
                assert inf == (ig + ih) / 2 + control
                assert hhi - (hg + hh) / 2 - 4 * control <= Q(1, 2)
                assert hhi <= 4 * inf
                if not cg and not ch:
                    assert hhi <= 4 * inf - Q(3, 2)
                checked += 1
        total_pairs += checked
        print(f'{n} data bits: {len(eligible)} eligible branches, {checked} ordered pairs certified.')
    print('Total certified small pairs:', total_pairs)


def bent_values(a, b, m):
    g_exponent = sum(((a >> (2 * j)) & 1) * ((a >> (2 * j + 1)) & 1) for j in range(m))
    h_exponent = (a & b).bit_count()
    return (-1 if g_exponent % 2 else 1), (-1 if h_exponent % 2 else 1)


def alternating_list_truth(m, controls):
    data_bits = 2 * m
    mask = (1 << data_bits) - 1
    values = []
    for point in range(1 << (controls + 4 * m)):
        selector = point & ((1 << controls) - 1)
        a = (point >> controls) & mask
        b = point >> (controls + data_bits)
        g, h = bent_values(a, b, m)
        selected = controls
        for j in range(controls):
            if not ((selector >> j) & 1):
                selected = j
                break
        values.append(g if selected % 2 == 0 else h)
    return values


def check_bent_selectors():
    for m in range(1, 4):
        w = walsh(alternating_list_truth(m, 1))
        size = len(w)
        r, n = 1 << m, 1 << (2 * m)
        unit = size // (1 << (2 * m + 1))
        expected = Counter()
        expected[(r + 1) * unit] += n
        expected[(r - 1) * unit] += n
        expected[unit] += 2 * n * (n - 1)
        assert Counter(map(abs, w)) == expected
        assert all(w)
        assert (r + 1) > 1 and (r + 1) % 2 == 1
        inf = influence(w)
        assert inf == Q(3 * m, 2) + Q(1, 2) - Q(1, 2 * n)
        hlo, hhi = entropy_interval(w)
        assert hhi <= 4 * inf - Q(3, 2)
        print(f'bent selector m={m}: {4*m+1} bits, I={inf}, H in [{float(hlo):.12f},{float(hhi):.12f}], odd factor={r+1}')


def check_lists():
    for m in (1, 2):
        for controls in range(1, 7):
            w = walsh(alternating_list_truth(m, controls))
            inf = influence(w)
            hlo, hhi = entropy_interval(w)
            assert hhi <= 4 * inf - 1 - Q(1, 1 << controls)
            h_count = sum(1 << (controls - j - 1) for j in range(controls) if j % 2)
            h_count += controls % 2  # fallback h exactly for odd length
            target_mask = 1 << (controls + 2 * m)  # U=0, V=e_1, no controls
            assert abs(w[target_mask]) == h_count * (1 << (2 * m))
            if controls >= 3:
                assert h_count > 1 and h_count % 2 == 1
            print(f'first-hit list m={m}, k={controls}: exact Walsh and FEI-4/slack certified; odd part={h_count}')


def check_unpaid_selector_counterexample():
    positive = {0, 1, 2, 3, 4, 5, 8, 10}
    truth = [1 if s in positive else -1 for s in range(16)]
    w = walsh(truth)
    assert w == [0, 4, 4, 0, 8, 4, -4, 0, 8, -4, 4, 0, 0, -4, -4, 0]
    assert entropy_interval(w) == (Q(3), Q(3))
    assert influence(w) == Q(3, 2)
    h, inf = Q(0), Q(1)  # literal at depth zero
    for depth in range(1, 5):
        h, inf = 3 + Q(3, 2) * h, Q(3, 2) * inf
        assert h == 6 * ((Q(3, 2) ** depth) - 1)
        assert inf == Q(3, 2) ** depth
        if depth == 3:
            assert h / inf == Q(38, 9)
    assert h == Q(195, 8) and inf + 1 == Q(97, 16)
    assert h - 4 * (inf + 1) == Q(1, 8)
    print('Unpaid forest-selector counterexample: H=195/8, I=97/16, H-4I=1/8.')


def main():
    check_polynomial_certificate()
    check_small_pairs()
    check_bent_selectors()
    check_lists()
    check_unpaid_selector_counterexample()
    print('All exact interpolation certificates passed.')


if __name__ == '__main__':
    main()
