#!/usr/bin/env python3
"""Verify one fixed nonsimple odd Bol-folder countercontrol, without searching.

F = F_3[t]/(t^3-t+1), E = F[i]/(i^2+1); G = E^+ : C_7.
The checks below certify only this finite example, not a simple-loop theorem.
"""

from itertools import product

F = tuple(product(range(3), repeat=3))
ZERO = (0, 0, 0)
ONE = (1, 0, 0)
T = (0, 1, 0)
T2 = (0, 0, 1)


def add(x, y):
    return tuple((a + b) % 3 for a, b in zip(x, y))


def neg(x):
    return tuple(-a % 3 for a in x)


def mul(x, y):
    c = [0] * 5
    for j in range(3):
        for k in range(3):
            c[j + k] = (c[j + k] + x[j] * y[k]) % 3
    for j in (4, 3):  # t^3 = t - 1
        c[j - 3] = (c[j - 3] - c[j]) % 3
        c[j - 2] = (c[j - 2] + c[j]) % 3
    return tuple(c[:3])


def ep_add(x, y):
    return add(x[0], y[0]), add(x[1], y[1])


def ep_neg(x):
    return neg(x[0]), neg(x[1])


def ep_mul(x, y):
    return (add(mul(x[0], y[0]), neg(mul(x[1], y[1]))),
            add(mul(x[0], y[1]), mul(x[1], y[0])))


def power(x, n, multiply, unit):
    result = unit
    while n:
        if n & 1:
            result = multiply(result, x)
        x = multiply(x, x)
        n //= 2
    return result


def linear_f(x):
    # f(1)=0, f(t)=t+t^2, f(t^2)=2t^2.
    return (0, x[1], (x[1] + 2 * x[2]) % 3)


def determinant(columns):
    a, b, c = columns
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
            - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0])) % 3


def main():
    # A cubic over F_3 is irreducible iff it has no F_3 root.
    assert all((x ** 3 - x + 1) % 3 for x in range(3))
    assert neg(ONE) not in {mul(x, x) for x in F}
    e_zero, e_one = (ZERO, ZERO), (ONE, ZERO)
    E = tuple(product(F, repeat=2))
    zeta = ((0, 0, 2), (0, 1, 1))
    assert zeta != e_one and power(zeta, 7, ep_mul, e_one) == e_one
    assert ep_mul(zeta, (zeta[0], neg(zeta[1]))) == e_one
    zp = tuple(power(zeta, j, ep_mul, e_one) for j in range(7))
    assert len(set(zp)) == 7

    W = {(x, linear_f(x)) for x in F}
    assert len(W) == 27 and e_zero in W
    assert all(ep_add(x, y) in W for x in W for y in W)
    conjugates = tuple({ep_mul(z, w) for w in W} for z in zp)
    tau_W = {(x, neg(y)) for x, y in W}
    assert len(set(map(frozenset, conjugates))) == 7
    assert all(tau_W != subspace for subspace in conjugates)
    determinants = tuple(determinant(tuple(add(mul(a, x), mul(b, linear_f(x)))
                                             for x in (ONE, T, T2)))
                         for a, b in zp)
    assert determinants == (1, 1, 2, 2, 2, 1, 2)
    anti = {(ZERO, x) for x in F}
    assert all(W & {ep_mul(z, x) for x in anti} == {e_zero} for z in zp)
    assert set.intersection(*conjugates) == {e_zero}  # core of H in G

    # Semidirect coordinates (v,j), multiplication (v,j)(w,k)=(v+zeta^j w,j+k).
    def group_mul(x, y):
        return ep_add(x[0], ep_mul(zp[x[1]], y[0])), (x[1] + y[1]) % 7

    def group_inverse(x):
        return ep_neg(ep_mul(zp[-x[1] % 7], x[0])), -x[1] % 7

    def tau(x):
        (a, b), j = x
        return (a, neg(b)), -j % 7

    identity = (e_zero, 0)
    K = {(v, j) for v in E for j in range(7) if tau((v, j)) == group_inverse((v, j))}
    assert len(K) == 189 and identity in K
    assert all(group_inverse(x) in K for x in K)
    assert all(group_mul(group_mul(x, y), x) in K for x in K for y in K)
    # The seven H^g are zeta^j W; verify all left cosets directly.
    for subspace in conjugates:
        products = {group_mul(k, (h, 0)) for k in K for h in subspace}
        assert len(products) == 7 * len(E)

    # (0,a) in K and the a-conjugates of (i,1) span E additively.
    assert (e_zero, 1) in K and ((ZERO, ONE), 0) in K
    span = {e_zero}
    for z in zp:
        v = ep_mul(z, (ZERO, ONE))
        span = {ep_add(s, ep_mul((c, ZERO), v))
                for s in span for c in ((0, 0, 0), (1, 0, 0), (2, 0, 0))}
    assert len(span) == len(E)
    assert sum(1 for v, j in K if j == 0) == 27
    # H≤V and K projects onto C7: quotient loop of order 7, kernel size 27.
    print('field checks: irreducible cubic, nonsquare -1, zeta order 7 and norm 1')
    print('subspaces: determinants 1 1 2 2 2 1 2; tau(H) differs from all 7 conjugates; core 1')
    print('folder: |G|=5103, |H|=27, |K|=189; transversals, closure and generation verified')
    print('scope: non-Bruck, nonsimple control; quotient order 7 and kernel order 27')


if __name__ == '__main__':
    main()
