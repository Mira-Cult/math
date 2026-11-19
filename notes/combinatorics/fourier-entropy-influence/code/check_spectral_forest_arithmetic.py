#!/usr/bin/env python3
"""Exact certificates for the spectral-forest arithmetic research note.

Only the Python standard library is required.  This script verifies explicit
constructions; it is not a proof of a universal Fourier entropy inequality.
"""
from fractions import Fraction
from collections import Counter


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


def valuation(s):
    a, b, c, d = [(s >> i) & 1 for i in range(4)]
    return 3 - 2 * a - 2 * b - c + a * b + b * c + c * d


def prefix_bent_completion(lengths, core_bits, shift=0):
    """Complete p_s=4**(-lengths[s]) with independent fair spectral bits.

    The canonical four-ary code occupies consecutive aligned address intervals.
    Its free suffix bits carry the standard quadratic bent phase.
    """
    depth = max(lengths.values(), default=0)
    address_bits = 2 * depth
    address_size = 1 << address_bits
    cursor = 0
    allocation = {}
    for s, d in sorted(lengths.items(), key=lambda item: (item[1], item[0])):
        width = 1 << (2 * (depth - d))
        assert cursor % width == 0
        assert cursor + width <= address_size
        for z in range(cursor, cursor + width):
            assert z not in allocation
            allocation[z] = (s, address_bits - 2 * d)
        cursor += width
    assert cursor == address_size
    values = []
    for z in range(address_size):
        s, free_bits = allocation[z]
        exponent = sum(((z >> j) & 1) * ((z >> (j + 1)) & 1)
                       for j in range(0, free_bits, 2))
        for x in range(1 << core_bits):
            values.append((-1) ** (exponent + ((s ^ shift) & x).bit_count()))
    return values, address_bits


def statistics_from_dyadic_walsh(coefficients):
    size = len(coefficients)
    n = size.bit_length() - 1
    assert size == 1 << n
    assert sum(w * w for w in coefficients) == size * size
    entropy = Fraction(0)
    influence = Fraction(0)
    for s, w in enumerate(coefficients):
        if not w:
            continue
        a = abs(w)
        assert a & (a - 1) == 0
        exponent = a.bit_length() - 1
        probability = Fraction(w * w, size * size)
        entropy += probability * (2 * n - 2 * exponent)
        influence += probability * s.bit_count()
    return entropy, influence


def main():
    v = [valuation(s) for s in range(16)]
    assert v == [3, 1, 1, 0, 2, 0, 1, 0, 3, 1, 1, 0, 3, 1, 2, 1]
    amplitude = [1 << e for e in v]
    assert sum(a * a for a in amplitude) == 256
    p = [Fraction(a * a, 256) for a in amplitude]
    base_entropy = sum(p[s] * (8 - 2 * v[s]) for s in range(16))
    assert base_entropy == Fraction(89, 32)
    print('core valuation counts:', dict(sorted(Counter(v).items())))
    print('core H:', base_entropy)
    lengths = {s: 4 - v[s] for s in range(16)}
    for shift in [0, 8]:
        truth, m = prefix_bent_completion(lengths, 4, shift=shift)
        transformed = walsh(truth)
        n = 4 + m
        for mask, w in enumerate(transformed):
            core_s = (mask & 15) ^ shift
            expected = 1 << (4 + m // 2 - lengths[core_s])
            assert abs(w) == expected
        entropy, influence = statistics_from_dyadic_walsh(transformed)
        base_influence = sum(p[s] * (s ^ shift).bit_count() for s in range(16))
        assert entropy == base_entropy + m
        assert influence == base_influence + Fraction(m, 2)
        if shift == 0:
            assert base_influence == Fraction(163, 128)
            assert influence == Fraction(675, 128)
            assert entropy / influence == Fraction(92, 45)
        else:
            assert base_influence == Fraction(65, 64)
            assert influence == Fraction(321, 64)
            assert entropy / influence == Fraction(230, 107)
        print('Boolean completion:', {'n': n, 'core_shift': shift,
              'Walsh_magnitudes': sorted(set(map(abs, transformed))),
              'H': str(entropy), 'I': str(influence),
              'H/I': str(entropy / influence)})
    # Arity three really permits an odd prime in the primitive amplitudes.
    and_phase = [-1] + [1] * 7
    w3 = walsh(and_phase)
    assert sorted(map(abs, w3)) == [2] * 7 + [6]
    assert sum((abs(w) // 2) ** 2 for w in w3) == 16
    print('three-bit AND primitive amplitudes:', [abs(w) // 2 for w in w3])
    print('All exact certificates passed.')


if __name__ == '__main__':
    main()
