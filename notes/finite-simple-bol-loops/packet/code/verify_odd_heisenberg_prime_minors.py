#!/usr/bin/env python3
"""Exact base Fourier-minor controls for q=7,19; Python 3.11+, no packages.

The prime-family theorem remains conditional on its base-minor hypothesis.
"""
from math import gcd

assert __debug__


def verify(q):
    d = q - 1
    assert all(pow(3, k, q) != 1 for k in range(1, d))
    assert pow(3, d, q) == 1 and pow(3, d // 2, q) == q - 1
    zero = (0,) * d
    one = (1,) + (0,) * (d - 1)
    zeta = (0, 1) + (0,) * (d - 2)

    def mul(a, b):
        c = [0] * (2*d - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                c[i+j] += x*y
        # Reduce modulo Phi_q=1+X+...+X^(q-1).
        for k in range(2*d - 2, d - 1, -1):
            t = c[k] % 3
            for j in range(d):
                c[k-d+j] -= t
        return tuple(x % 3 for x in c[:d])

    def power(x, n):
        result = one
        while n:
            if n & 1:
                result = mul(result, x)
            x = mul(x, x)
            n //= 2
        return result

    def rank(matrix):
        a = [row[:] for row in matrix]
        row = 0
        for col in range(len(a[0])):
            pivot = next((i for i in range(row, len(a)) if a[i][col] != zero), None)
            if pivot is None:
                continue
            a[row], a[pivot] = a[pivot], a[row]
            inv = power(a[row][col], 3**d - 2)
            a[row] = [mul(x, inv) for x in a[row]]
            for i in range(row + 1, len(a)):
                scale = a[i][col]
                a[i] = [tuple((u-v) % 3 for u, v in zip(x, mul(scale, y)))
                        for x, y in zip(a[i], a[row])]
            row += 1
            if row == len(a):
                break
        return row

    powers = [power(zeta, k) for k in range(q)]
    residues = sorted({k*k % q for k in range(1, q)})
    nonresidues = sorted(set(range(1, q)) - set(residues))
    expected = (q-1)//2
    actual = rank([[powers[i*j % q] for j in residues] for i in nonresidues])
    assert actual == expected

    def add(a, b):
        return tuple((x+y) % 3 for x, y in zip(a, b))

    period_r = zero
    period_n = zero
    for j in residues:
        period_r = add(period_r, powers[j])
    for j in nonresidues:
        period_n = add(period_n, powers[j])
    assert add(period_r, period_n) == tuple((-x) % 3 for x in one)
    assert mul(period_r, period_n) == tuple((-x) % 3 for x in one)
    for v in range(q):
        wbar = [zero] * q
        wbar[v] = one
        for r in residues:
            wbar[(v+r) % q] = mul(period_r, powers[(-v*r) % q])
        out = []
        for i in range(q):
            value = zero
            for j in range(q):
                value = add(value, mul(powers[i*j % q], wbar[j]))
            out.append(value)
        assert out[v] == powers[v*v % q]
        assert all(out[(v+j) % q] == zero for j in nonresidues)
    print(f'q={q}: base minor rank {actual}; period and support identities verified')


if __name__ == '__main__':
    verify(7)
    verify(19)
    for q, m, expected in ((7, 3, 9), (19, 9, 2193)):
        order = 3**m + 1
        summands = [gcd(9**k - 1, order) - gcd(9**k - 1, q)
                    for k in range(m)]
        assert sum(summands) == m*expected
        print(f'q={q}: within-family isomorphism classes {expected}')
