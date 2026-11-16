#!/usr/bin/env python3
"""Fixed quotient/module controls for odd-metabelian Heisenberg data.

No external packages, output files, or search over loop multiplications.
Run with Python 3.11+ and assertions enabled.
"""
from collections import Counter
from itertools import product

assert __debug__
P, Q = 3, 7
ELEMENTS = list(product(range(Q), range(Q), range(Q), range(P)))
ONE_GROUP = (0, 0, 0, 0)


def mul(g, h):
    u, v, z, i = g
    x, y, w, j = h
    x = x * pow(2, i, Q) % Q
    y = y * pow(2, -i, Q) % Q
    return ((u + x) % Q, (v + y) % Q,
            (z + w + 4 * (u * y - v * x)) % Q, (i + j) % P)


def inverse(g):
    u, v, z, i = g
    return (-u * pow(2, -i, Q) % Q, -v * pow(2, i, Q) % Q,
            -z % Q, -i % P)


def theta(g):
    u, v, z, i = g
    return v, u, -z % Q, -i % P


def power(g, n):
    a = ONE_GROUP
    for _ in range(n):
        a = mul(a, g)
    return a


def quotient_control():
    j = [(u, 0, 0, i) for u in range(Q) for i in range(P)]
    inverted = {g for g in ELEMENTS if theta(g) == inverse(g)}
    conjugates = {
        frozenset(mul(mul(inverse(g), h), g) for h in j)
        for g in ELEMENTS
    }
    assert len(ELEMENTS) == 1029 and len(j) == 21
    assert len(inverted) == 147 and len(conjugates) == 7
    for h in conjugates:
        remaining = set(ELEMENTS)
        count = 0
        while remaining:
            g = next(iter(remaining))
            coset = {mul(g, x) for x in h}
            assert len(coset) == 21 and len(coset & inverted) == 3
            remaining.difference_update(coset)
            count += 1
        assert count == 49
    print('quotient: order 1029, inverted 147, 7 conjugates, 49 cosets each, multiplicity 3')


ZERO = (0,) * 6
ONE = (1, 0, 0, 0, 0, 0)
ZETA = (0, 1, 0, 0, 0, 0)


def add(a, b):
    return tuple((x + y) % 3 for x, y in zip(a, b))


def neg(a):
    return tuple(-x % 3 for x in a)


def field_mul(a, b):
    # F_3[z]/(1+z+...+z^6).
    c = [0] * 11
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] = (c[i + j] + x * y) % 3
    for i in range(10, 5, -1):
        x = c[i]
        for j in range(6):
            c[i - 6 + j] = (c[i - 6 + j] - x) % 3
    return tuple(c[:6])


def field_pow(x, n):
    y = ONE
    while n:
        if n & 1:
            y = field_mul(y, x)
        x = field_mul(x, x)
        n //= 2
    return y


ZETA_POWERS = [field_pow(ZETA, i) for i in range(7)]


def sigma(v):
    result = []
    for i in range(7):
        total = ZERO
        for j in range(7):
            total = add(total, field_mul(ZETA_POWERS[i * j % 7], field_pow(v[j], 27)))
        result.append(total)
    return result


def rho(v, g):
    """Action of BCH-coordinate g=(u,v,z,i) via ordered x^u y^v z^k a^i."""
    u, w, z, i = g
    ordered_z = (z - 4 * u * w) % 7
    result = [ZERO] * 7
    for j in range(7):
        k = (pow(4, i, 7) * j + w) % 7
        result[k] = field_mul(ZETA_POWERS[(ordered_z + u * k) % 7], v[j])
    return result


def basis_vector(i):
    v = [ZERO] * 7
    v[i // 6] = tuple(int(j == i % 6) for j in range(6))
    return v


def module_control():
    assert field_pow(ZETA, 7) == ONE and len(set(ZETA_POWERS)) == 7
    gens = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    assert power(gens[0], 7) == power(gens[1], 7) == power(gens[2], 7) == ONE_GROUP
    assert power(gens[3], 3) == ONE_GROUP
    for i in range(42):
        v = basis_vector(i)
        assert sigma(sigma(v)) == v
        for g in gens:
            assert sigma(rho(sigma(v), g)) == rho(v, theta(g))
            for h in gens:
                assert rho(rho(v, h), g) == rho(v, mul(g, h))
    plus_columns = [[x for a, b in zip(v, sigma(v)) for x in add(a, b)]
                    for v in map(basis_vector, range(42))]
    assert rank(plus_columns) == 21
    print('module: dimension 42, fixed dimension 21, relations and involution compatibility verified')


def rank(columns):
    matrix = [[col[i] for col in columns] for i in range(42)]
    row = 0
    for j in range(len(columns)):
        pivot = next((k for k in range(row, 42) if matrix[k][j]), None)
        if pivot is None:
            continue
        matrix[row], matrix[pivot] = matrix[pivot], matrix[row]
        if matrix[row][j] == 2:
            matrix[row] = [(2 * x) % 3 for x in matrix[row]]
        for k in range(42):
            if k != row and matrix[k][j]:
                scale = matrix[k][j]
                matrix[k] = [(x - scale * y) % 3 for x, y in zip(matrix[k], matrix[row])]
        row += 1
    return row


def avoidance_control():
    # W=Ue_0 direct-sum Ee_1 direct-sum Ee_2 direct-sum Ee_4.
    vectors = [basis_vector(6*j+k) for j in (1, 2, 4) for k in range(6)]
    for value in ((0, 0, 0, 0, 0, 1), (0, 0, 0, 1, 1, 0)):
        v = [ZERO] * 7
        v[0] = value
        vectors.append(v)
    assert len(vectors) == 20 and rank([[x for y in v for x in y] for v in vectors]) == 20
    flat = [[x for y in w for x in y] for w in vectors]
    for g in ((1, 0, 0, 0), (0, 0, 0, 1)):
        transformed = [[x for y in rho(w, g) for x in y] for w in vectors]
        assert rank(flat + transformed) == 20
    for u, v, z in product(range(7), repeat=3):
        columns = []
        for w in vectors:
            image = rho(w, (u, v, z, 0))
            columns.append([x for a, b in zip(image, sigma(image)) for x in add(a, b)])
        assert rank(columns) == 20
    print('module avoidance: one 20-space avoids all 343 marked negative eigenspaces')


if __name__ == '__main__':
    quotient_control()
    module_control()
    avoidance_control()
