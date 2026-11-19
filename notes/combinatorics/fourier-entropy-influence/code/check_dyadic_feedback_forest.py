#!/usr/bin/env python3
"""Exact finite checks for dyadic_feedback_forest_fei.md (standard library).

Examples, identities and exhaustive small cases are checked. This script
does not prove the universal class theorem or establish literature novelty.
"""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product


def walsh(values):
    out = list(values)
    step = 1
    while step < len(out):
        for first in range(0, len(out), 2 * step):
            for j in range(first, first + step):
                a, b = out[j], out[j + step]
                out[j], out[j + step] = a + b, a - b
        step *= 2
    return out


def dyadic(a):
    return a == 0 or (abs(a) & (abs(a) - 1)) == 0


def raw_numerators(W):
    """Return 4**n times H_*, I and squared norm for dyadic integer W."""
    n = len(W).bit_length() - 1
    assert len(W) == 1 << n and all(dyadic(a) for a in W)
    H = sum(a * a * (2 * n - 2 * (abs(a).bit_length() - 1))
            for a in W if a)
    I = sum(a * a * s.bit_count() for s, a in enumerate(W))
    return H, I, sum(a * a for a in W)


@lru_cache(maxsize=None)
def forest_on_coordinate_subcube(A):
    """Exact log-amplitude test; includes zero sections and fixed bits.

    General deterministic-edge quotients are not tested by this classifier;
    omitting them only decreases the number of eligible cases.
    """
    n = len(A).bit_length() - 1
    support = [s for s, a in enumerate(A) if a]
    if not support:
        return True
    free = [i for i in range(n)
            if any((s >> i & 1) != (support[0] >> i & 1) for s in support)]
    if len(support) != 1 << len(free):
        return False
    fixed = support[0] & ~sum(1 << i for i in free)
    logs = []
    for z in range(1 << len(free)):
        s = fixed | sum(((z >> j) & 1) << i for j, i in enumerate(free))
        a = A[s]
        if not a or not dyadic(a):
            return False
        logs.append(abs(a).bit_length() - 1)
    coeff = logs[:]
    for i in range(len(free)):
        for s in range(len(coeff)):
            if s >> i & 1:
                coeff[s] -= coeff[s ^ (1 << i)]
    if any(c and s.bit_count() > 2 for s, c in enumerate(coeff)):
        return False
    parent = list(range(len(free)))

    def root(x):
        while parent[x] != x:
            x = parent[x]
        return x

    for s, c in enumerate(coeff):
        if not c or s.bit_count() != 2:
            continue
        i, j = [i for i in range(len(free)) if s >> i & 1]
        a, b = root(i), root(j)
        if a == b:
            return False
        parent[a] = b
    return True


def row(W, K, a):
    n = len(W).bit_length() - 1
    R = [i for i in range(n) if i not in K]
    base = sum(((a >> j) & 1) << i for j, i in enumerate(K))
    return [W[base | sum(((t >> j) & 1) << i for j, i in enumerate(R))]
            for t in range(1 << len(R))]


def exhaustive_boolean():
    checked = eligible = sections = 0
    for n in range(5):
        for values in product((-1, 1), repeat=1 << n):
            checked += 1
            W = walsh(values)
            if not all(dyadic(a) for a in W):
                continue
            H, I, norm = raw_numerators(W)
            assert norm == 4 ** n
            for k in range(1, min(2, n) + 1):
                for K in combinations(range(n), k):
                    rows = [row(W, K, a) for a in range(1 << k)]
                    if not all(forest_on_coordinate_subcube(tuple(map(abs, r)))
                               for r in rows):
                        continue
                    eligible += 1
                    I_R = sum(a * a * (s & ~sum(1 << i for i in K)).bit_count()
                              for s, a in enumerate(W))
                    assert H <= 4 * I_R + (2 * k - 2) * norm
                    # W_h=W_f/2 for h_a=2**(k-1)g_a, independently of k.
                    for r in rows:
                        assert all(a % 2 == 0 for a in r)
                        W_h = [a // 2 for a in r]
                        vals = walsh(W_h)
                        assert all(v % len(r) == 0 for v in vals)
                        hvals = [v // len(r) for v in vals]
                        assert walsh(hvals) == W_h
                        hH, hI, _ = raw_numerators(W_h)
                        assert hH <= 4 * hI
                        sections += 1
    print('Boolean functions:', checked, 'eligible cutsets:', eligible,
          'exact integer sections:', sections, flush=True)


def exhaustive_integer():
    checked = eligible = 0
    for n in range(4):
        for values in product((-1, 0, 1), repeat=1 << n):
            checked += 1
            W = walsh(values)
            if not all(dyadic(a) for a in W):
                continue
            if not forest_on_coordinate_subcube(tuple(map(abs, W))):
                continue
            eligible += 1
            for scale in (1, 2, 8):
                H, I, _ = raw_numerators([scale * a for a in W])
                assert H <= 4 * I
    print('Ternary integer functions:', checked, 'eligible forest sections:',
          eligible, 'scales: 1,2,8', flush=True)


def prefix_bent_completion(lengths, core_bits, shift=0):
    """Existing Kraft-prefix construction, reproduced without imports."""
    depth = max(lengths.values(), default=0)
    address_bits = 2 * depth
    allocation = {}
    cursor = 0
    for s, d in sorted(lengths.items(), key=lambda item: (item[1], item[0])):
        width = 1 << (2 * (depth - d))
        assert cursor % width == 0
        for z in range(cursor, cursor + width):
            allocation[z] = (s, address_bits - 2 * d)
        cursor += width
    assert cursor == 1 << address_bits
    truth = []
    for z in range(1 << address_bits):
        s, free_bits = allocation[z]
        bent_exponent = sum((z >> j & 1) * (z >> (j + 1) & 1)
                            for j in range(0, free_bits, 2))
        for x in range(1 << core_bits):
            truth.append((-1) ** (bent_exponent + ((s ^ shift) & x).bit_count()))
    return truth, address_bits


def genuine_cycle():
    v = []
    for s in range(16):
        a, b, c, d = [(s >> i) & 1 for i in range(4)]
        v.append(1 - a + c - d + a*b - b*c + 2*c*d + d*a)
    assert v == [1, 0, 1, 1, 2, 1, 1, 1, 0, 0, 0, 1, 3, 3, 2, 3]
    assert sum(4 ** z for z in v) == 256
    assert not forest_on_coordinate_subcube(tuple(1 << z for z in v))
    path = [3, 1, 1, 0, 2, 0, 1, 0, 3, 1, 1, 0, 3, 1, 2, 1]
    for s in range(16):
        a = sum(((s & r).bit_count() % 2) << i
                for i, r in enumerate((4, 12, 5, 3)))
        assert path[a ^ 9] == v[s]
    marginals = [Fraction(73,128), Fraction(101,256),
                 Fraction(59,64), Fraction(215,256)]
    assert [sum(Fraction(4**v[s],256) for s in range(16) if s >> i & 1)
            for i in range(4)] == marginals
    for shift in (0, 13):
        truth, m = prefix_bent_completion({s: 4-v[s] for s in range(16)}, 4, shift)
        W = walsh(truth)
        assert m == 8 and len(truth) == 4096 and set(truth) == {-1, 1}
        for s, a in enumerate(W):
            assert abs(a) == 1 << (4 + v[(s & 15) ^ shift])
        H, I, norm = raw_numerators(W)
        assert norm == 4**12
        assert Fraction(H,norm) == Fraction(345,32)
        assert Fraction(I,norm) == (Fraction(861,128) if shift == 0 else Fraction(81,16))
        for i in range(4):
            rows = [row(W, (i,), a) for a in range(2)]
            assert all(forest_on_coordinate_subcube(tuple(map(abs, r))) for r in rows)
            I_R = sum(a*a*(s & ~(1 << i)).bit_count() for s,a in enumerate(W))
            assert H <= 4*I_R - 2*norm
        print('Genuine cycle:', {'n':12, 'shift':shift,
              'H':str(Fraction(H,norm)), 'I':str(Fraction(I,norm)),
              'H/I':str(Fraction(H,I))}, flush=True)
    assert 16**2 > 2*9**2   # log2(16/9)>1/2.
    assert 9**2 < 2**7     # log2(9)<7/2.
    assert list(map(abs, walsh([0,1,1,1]))) == [3,1,1,1]
    assert list(map(abs, walsh([-1]+[1]*7))) == [6,2,2,2,2,2,2,2]
    print('Odd-factor counterexamples: exact strict log inequalities passed.', flush=True)


if __name__ == '__main__':
    genuine_cycle()
    exhaustive_integer()
    exhaustive_boolean()
    print('All exact checks passed. Finite evidence is not the universal proof.')
