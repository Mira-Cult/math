#!/usr/bin/env python3
"""Exact controls for forest_slack_continuation.md.

Default parameters: every Boolean truth table on n=0,1,2,3,4 variables;
positive energy stars with N=1,...,12 leaves (direct state sums through N=8);
integer hard-zero bent star N=16, M=2 (131072 physical inputs);
the existing 7-bit genuine hard-zero path witness with central pair cut;
a 6-bit Boolean product-of-two-stars counterexample to free recursive cuts.

All assertions use integers or fractions. No floating-point comparison is used.
The asymptotic obstruction is proved in the manuscript, not inferred here.
"""
from fractions import Fraction
from itertools import combinations


def fwht(values):
    a = list(values)
    step = 1
    while step < len(a):
        for base in range(0, len(a), 2 * step):
            for j in range(base, base + step):
                x, y = a[j], a[j + step]
                a[j], a[j + step] = x + y, x - y
        step *= 2
    return a


def insert_pair(rest, rest_positions, i, j, pair):
    s = ((pair & 1) << i) | ((pair >> 1) << j)
    for r, position in enumerate(rest_positions):
        s |= ((rest >> r) & 1) << position
    return s


def forbidden_pair_checks():
    functions = sections = 0
    for n in range(5):
        size = 1 << n
        for truth in range(1 << size):
            f = [1 if (truth >> x) & 1 else -1 for x in range(size)]
            spectrum = fwht(f)
            functions += 1
            for i, j in combinations(range(n), 2):
                present = {((s >> i) & 1) | (((s >> j) & 1) << 1)
                           for s, value in enumerate(spectrum) if value}
                if len(present) == 4:
                    continue
                rest_positions = [r for r in range(n) if r not in (i, j)]
                for rest in range(1 << (n - 2)):
                    values = [f[insert_pair(rest, rest_positions, i, j, pair)]
                              for pair in range(4)]
                    numerator = fwht(values)
                    assert sorted(map(abs, numerator)) == [0, 0, 0, 4]
                    assert all(numerator[a] == 0 for a in set(range(4)) - present)
                    sections += 1
    assert functions == 65814
    print(f"Forbidden-pair lemma: {functions} Boolean functions; "
          f"{sections} admissible physical sections; PASS")


def energy_star_checks():
    for leaves in range(1, 13):
        theta = Fraction(4 * 5 ** leaves, 4 * 5 ** leaves + 2 ** leaves)
        slack = theta * (1 + Fraction(leaves, 5)) + (1 - theta) * 2
        target = 1 + Fraction(leaves, 5)
        assert target - slack == (1 - theta) * (Fraction(leaves, 5) - 1)
        assert (slack < target) == (leaves > 5)
        if leaves <= 8:
            total = cost = 0
            for s in range(1 << (leaves + 1)):
                root = s & 1
                ones = (s >> 1).bit_count()
                v = (1 - root) * (1 + leaves - ones)
                weight = 4 ** v
                total += weight
                cost += weight * (v + 2 * (root + ones))
            assert Fraction(cost, total) - leaves == slack
    print("Positive energy stars: 12 exact cases, 8 direct sums; PASS")


def integer_zero_star_check():
    leaves, magnitude = 16, 2
    size = 1 << (leaves + 1)
    truth = []
    for x in range(size):
        parity = sum(((x >> (2 * j)) & 3) == 3 for j in range(leaves // 2)) % 2
        bent = (-1) ** parity
        u = 1 if not ((x >> leaves) & 1) else -1
        truth.append(bent + magnitude * u)
    spectrum = fwht(truth)
    small = 1 << (leaves // 2 + 1)
    large = magnitude * size
    assert all(abs(spectrum[s]) == small for s in range(1 << leaves))
    assert spectrum[1 << leaves] == large
    assert all(spectrum[s] == 0 for s in range((1 << leaves) + 1, size))
    assert sum(x * x for x in truth) == size * (1 + magnitude ** 2)
    influence = Fraction(sum(s.bit_count() * a * a for s, a in enumerate(spectrum)),
                         size * size)
    assert influence == Fraction(leaves, 2) + magnitude ** 2
    # All amplitudes have integer binary logarithms, so raw entropy is exact.
    entropy = sum(Fraction(a * a, size * size)
                  * (2 * ((leaves + 1) - (abs(a).bit_length() - 1)))
                  for a in spectrum if a)
    assert entropy == leaves - 2 * magnitude ** 2
    assert entropy <= 2 * influence
    print(f"Integer hard-zero star: N={leaves}, M={magnitude}, "
          f"{size} truth values; H_raw={entropy}, I={influence}; PASS")


def dominating_edge_witness():
    support = [s for s in range(16)
               if not (((s >> 1) & 1) and ((s >> 2) & 1))
               and not (((s >> 1) & 1) and (s & 1))
               and not (((s >> 2) & 1) and ((s >> 3) & 1))]
    assert len(support) == 8
    truth = [(-1) ** ((support[x >> 4] & (x & 15)).bit_count())
             for x in range(128)]
    spectrum = fwht(truth)
    assert sum(bool(a) for a in spectrum) == 64
    assert all(abs(a) == 16 for a in spectrum if a)
    influence = Fraction(sum(s.bit_count() * a * a for s, a in enumerate(spectrum)),
                         128 ** 2)
    assert influence == Fraction(11, 4)
    residual = Fraction(sum((s & ~6).bit_count() * a * a
                            for s, a in enumerate(spectrum)), 128 ** 2)
    assert residual == Fraction(9, 4)
    assert 6 <= 4 * residual
    rest_positions = [0, 3, 4, 5, 6]
    for pair in range(4):
        values = []
        for rest in range(32):
            numerator = fwht([truth[insert_pair(rest, rest_positions, 1, 2, b)]
                              for b in range(4)])[pair]
            assert numerator % 4 == 0
            values.append(numerator // 4)
        section = fwht(values)
        nz = [abs(a) for a in section if a]
        if pair == 3:
            assert not nz
        else:
            assert nz and all(a == nz[0] for a in nz)
            # Each support is a coordinate subcube, hence the conditional law
            # is a product of fair and fixed spectral bits.
            present = [s for s, a in enumerate(section) if a]
            allowed = [{(s >> i) & 1 for s in present} for i in range(5)]
            assert len(present) == 2 ** sum(len(a) == 2 for a in allowed)
    print("Dominating forbidden edge: existing 7-bit path; exact integral "
          "sections and H=6 <=4 I_out=9; PASS")


def genuine_forest_iteration_counterexample():
    h = [-1, -1, -1, 0, 0, 0, 0, 1]
    k = [0, 0, 0, -1, 1, 1, 1, 0]
    wh, wk = fwht(h), fwht(k)
    assert wh == [-2, -2, -2, 2, -4, 0, 0, 0]
    assert wk == [2, 2, 2, -2, -4, 0, 0, 0]
    assert all(a * b == 0 and a * a + b * b == 1 for a, b in zip(h, k))
    truth = []
    for x in range(64):
        y = x & 7
        a = (-1) ** ((x >> 3) & 1)
        b = (-1) ** ((x >> 4) & 1)
        v = (x >> 5) & 1
        truth.append(a * h[y] + k[y] * (1 if v == 0 else b))
    assert all(a in (-1, 1) for a in truth)
    spectrum = fwht(truth)
    for t in range(8):
        for aux in range(8):
            expected = 0
            if aux == 1:
                expected = 8 * wh[t]
            elif not (aux & 1):
                beta, gamma = (aux >> 1) & 1, (aux >> 2) & 1
                expected = 4 * (-1) ** (beta * gamma) * wk[t]
            assert spectrum[t | (aux << 3)] == expected
    assert sum(bool(a) for a in spectrum) == 25
    assert Fraction(sum(s.bit_count() * a * a for s, a in enumerate(spectrum)),
                    64 ** 2) == 2
    entropy = sum(Fraction(a * a, 64 ** 2) * (2 * (6 - (abs(a).bit_length() - 1)))
                  for a in spectrum if a)
    assert entropy == 4
    # First cut the forbidden auxiliary edge {a,b}; frequency10 gives h.
    for y in range(8):
        for v in range(2):
            numerator = sum(truth[y | (a << 3) | (b << 4) | (v << 5)] * (-1) ** a
                            for a in range(2) for b in range(2))
            assert numerator == 4 * h[y]
    # Second cut the genuine forbidden y-edge {y0,y2}.
    sections = []
    for pair in range(4):
        values = []
        for y1 in range(2):
            numerator = fwht([h[insert_pair(y1, [1], 0, 2, b)] for b in range(4)])[pair]
            values.append(Fraction(numerator, 4))
        sections.append(values)
    assert sections == [[Fraction(-1, 2), 0], [0, Fraction(-1, 2)],
                        [Fraction(-1, 2), Fraction(-1, 2)], [0, 0]]
    print("Genuine Boolean forest noniterability: 64 truth values, 25 atoms, "
          "two forbidden-edge cuts; exact half-sections; PASS")


def iteration_counterexample():
    # Physical order (x,y): (1,1),(-1,1),(1,-1),(-1,-1).
    ternary = [1, 0, 0, -1]
    assert fwht(ternary) == [0, 2, 2, 0]
    assert Fraction(fwht(ternary)[1], 4) == Fraction(1, 2)
    print("Noniterability counterexample: exact ternary half-sections; PASS")


if __name__ == "__main__":
    forbidden_pair_checks()
    energy_star_checks()
    integer_zero_star_check()
    dominating_edge_witness()
    genuine_forest_iteration_counterexample()
    iteration_counterexample()
