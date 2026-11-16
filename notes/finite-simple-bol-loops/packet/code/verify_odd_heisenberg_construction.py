#!/usr/bin/env python3
"""Exact affine-fiber certificate for the odd Heisenberg candidate (Python 3.11+).

Imports the neighboring quotient/module control. Assertions must be enabled.
No third-party packages, random search, or generated files are used.
"""
from itertools import product
from verify_odd_heisenberg_control import (
    ELEMENTS, ONE_GROUP, ZERO, add, basis_vector, field_mul, field_pow,
    inverse, mul, quotient_control, module_control, rank, rho, sigma, theta,
)

assert __debug__
LAMBDA = (0, 0, 0, 1, 1, 2)
ALPHA = (0, 0, 0, 1, 1, 0)
U2 = (1, 2, 1, 2, 2, 2)
B = (1, 1, 2, 1, 0, 0)


def flatten(vector):
    return [x for item in vector for x in item]


def additive_minus(a):
    return tuple(-x % 3 for x in a)


def zero_weight(value):
    result = [ZERO] * 7
    result[0] = value
    return result


def nullspace(columns):
    """Annihilator in the 42-dimensional F3 dual of the column span."""
    matrix = [column[:] for column in columns]
    pivots = []
    row = 0
    for col in range(42):
        pivot = next((k for k in range(row, len(matrix)) if matrix[k][col]), None)
        if pivot is None:
            continue
        matrix[row], matrix[pivot] = matrix[pivot], matrix[row]
        if matrix[row][col] == 2:
            matrix[row] = [(2*x) % 3 for x in matrix[row]]
        for k in range(len(matrix)):
            if k != row and matrix[k][col]:
                scale = matrix[k][col]
                matrix[k] = [(x-scale*y) % 3 for x, y in zip(matrix[k], matrix[row])]
        pivots.append(col)
        row += 1
        if row == len(matrix):
            break
    free = [j for j in range(42) if j not in pivots]
    answer = []
    for col in free:
        vector = [0] * 42
        vector[col] = 1
        for i, pivot in enumerate(pivots):
            vector[pivot] = -matrix[i][col] % 3
        answer.append(vector)
    return answer


def verify():
    assert field_pow(ALPHA, 27) == ALPHA
    assert field_mul(LAMBDA, ALPHA) == U2
    assert field_mul(U2, ALPHA) == B
    w = [basis_vector(6*j+k) for j in (1, 2, 4) for k in range(6)]
    w.extend([zero_weight(LAMBDA), zero_weight(U2)])
    assert rank([flatten(v) for v in w]) == 20
    for h in [(1, 0, 0, 0), (0, 0, 0, 1)]:
        assert rank([flatten(v) for v in w] + [flatten(rho(v, h)) for v in w]) == 20
    # a fixes b; x fixes e_0.  This makes h -> i*b a cocycle on J,
    # for h=(u,0,0,i), and H/W a complement isomorphic to J.
    for h in [(1, 0, 0, 0), (0, 0, 0, 1)]:
        assert rho(zero_weight(B), h) == zero_weight(B)
    J = [(u, 0, 0, i) for u in range(7) for i in range(3)]
    Kbar = {g for g in ELEMENTS if theta(g) == inverse(g)}
    assert len(Kbar) == 147
    covered = set()
    for v0, z0 in product(range(7), repeat=2):
        t = (0, v0, z0, 0)
        coset = {mul(t, j) for j in J}
        assert not (coset & covered)
        covered.update(coset)
        selected = coset & Kbar
        assert len(selected) == 3
        tw = [flatten(rho(vector, t)) for vector in w]
        common = tw[:]
        by_label = {}
        for k in selected:
            j = mul(inverse(t), k)
            assert j in J
            label = j[3]
            assert label not in by_label
            by_label[label] = k
            negcols = []
            for idx in range(42):
                vector = basis_vector(idx)
                marked = rho(sigma(vector), k)  # rho(k) sigma, for the left fiber v k
                assert rho(sigma(marked), k) == vector
                negcols.append(flatten([add(a, additive_minus(b))
                                        for a, b in zip(vector, marked)]))
            assert rank(negcols) == 21
            assert rank(tw + negcols) == 41
            common.extend(negcols)
        assert set(by_label) == {0, 1, 2}
        assert rank(common) == 41
        dual = nullspace(common)
        assert len(dual) == 1
        tb = flatten(rho(zero_weight(B), t))
        value = sum(x*y for x, y in zip(dual[0], tb)) % 3
        assert value != 0
    assert covered == set(ELEMENTS)
    print('construction: 49 quotient cosets; each has 3 distinct parallel affine fibers; transversal verified')


def witness():
    """Check x(zx) != (xz)x using only the required section fibers."""
    w = [basis_vector(6*j+k) for j in (1, 2, 4) for k in range(6)]
    w.extend([zero_weight(LAMBDA), zero_weight(U2)])
    J = [(u, 0, 0, i) for u in range(7) for i in range(3)]
    invset = {g for g in ELEMENTS if theta(g) == inverse(g)}
    lookup = {}
    for v0, z0 in product(range(7), repeat=2):
        t = (0, v0, z0, 0)
        for j in J:
            l = mul(t, j)
            assert l not in lookup
            lookup[l] = t, j
    assert len(lookup) == len(ELEMENTS)

    def vec_add(v, w):
        return [add(a, b) for a, b in zip(v, w)]

    def vec_scale(v, c):
        return [tuple(c*x % 3 for x in a) for a in v]

    def solve(columns, target):
        matrix = [[columns[j][i] for j in range(len(columns))] + [target[i]]
                  for i in range(42)]
        pivots = []
        row = 0
        for col in range(len(columns)):
            pivot = next((k for k in range(row, 42) if matrix[k][col]), None)
            if pivot is None:
                continue
            matrix[row], matrix[pivot] = matrix[pivot], matrix[row]
            if matrix[row][col] == 2:
                matrix[row] = [(2*x) % 3 for x in matrix[row]]
            for k in range(42):
                if k != row and matrix[k][col]:
                    c = matrix[k][col]
                    matrix[k] = [(x-c*y) % 3 for x, y in zip(matrix[k], matrix[row])]
            pivots.append(col)
            row += 1
        assert row == 41
        if any(matrix[k][-1] for k in range(row, 42)):
            return None
        coeff = [0]*len(columns)
        for i, col in enumerate(pivots):
            coeff[col] = matrix[i][-1]
        return coeff

    def section(g):
        v, l = g
        t, j0 = lookup[l]
        bvec = zero_weight(B)
        base = vec_add(v, vec_scale(rho(bvec, t), -j0[3]))
        out = []
        for k in invset:
            tk, j = lookup[k]
            if tk != t:
                continue
            negcols = []
            for n in range(42):
                vector = basis_vector(n)
                marked = rho(sigma(vector), k)
                negcols.append(flatten([add(a, additive_minus(b))
                                        for a, b in zip(vector, marked)]))
            columns = negcols + [flatten(rho(vector, t)) for vector in w]
            rhs = flatten(vec_add(base, vec_scale(rho(bvec, t), j[3])))
            coeff = solve(columns, rhs)
            if coeff is not None:
                n = [sum(coeff[j]*negcols[j][i] for j in range(42)) % 3
                     for i in range(42)]
                out.append(([tuple(n[6*i:6*i+6]) for i in range(7)], k))
        assert len(out) == 1
        representative, k = out[0]
        assert vec_add(representative, rho(sigma(representative), k)) == [ZERO]*7
        j = mul(inverse(l), k)
        assert j in J
        difference = rho(vec_add(representative, vec_scale(v, -1)), inverse(l))
        difference = vec_add(difference, vec_scale(bvec, -j[3]))
        assert rank([flatten(vector) for vector in w] + [flatten(difference)]) == 20
        return representative, k

    def multiply(g, h):
        return vec_add(g[0], rho(h[0], g[1])), mul(g[1], h[1])

    def loop_product(g, h):
        return section(multiply(g, h))

    x = ([ZERO]*7, (0, 0, 1, 0))
    z = section((basis_vector(0), ONE_GROUP))
    left = loop_product(x, loop_product(z, x))
    right = loop_product(loop_product(x, z), x)
    assert left[1] == right[1] == (0, 0, 2, 1)
    assert left[0][0] == (0, 0, 0, 0, 2, 1)
    assert right[0][0] == (2, 0, 1, 0, 1, 2)
    assert left != right
    print('properness: x(zx) differs from (xz)x')


if __name__ == '__main__':
    quotient_control()
    module_control()
    verify()
    witness()
