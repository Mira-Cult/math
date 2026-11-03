#!/usr/bin/env python3
"""Certified independent cyclotomic units and a nonprincipal-prime control.

Author: /root/normalization. Standard library only. No approximate comparison
is trusted. Rational outward intervals certify every log determinant. These
are finite-index unit subgroups, not asserted full fundamental-unit bases.
"""
import argparse
import itertools
import json
from fractions import Fraction as F
from math import gcd, factorial

BITS = 160
GRID = 1 << BITS


def floorq(x):
    return x.numerator//x.denominator


def ceilq(x):
    return -((-x.numerator)//x.denominator)


def rounded(a, b):
    return (F(floorq(a*GRID), GRID), F(ceilq(b*GRID), GRID))


def exact(a):
    return (F(a), F(a))


def plus(x, y):
    return rounded(x[0]+y[0], x[1]+y[1])


def negative(x):
    return (-x[1], -x[0])


def minus(x, y):
    return plus(x, negative(y))


def times(x, y):
    vals = [a*b for a in x for b in y]
    return rounded(min(vals), max(vals))


def divided(x, y):
    assert y[0]*y[1] > 0, ('zero interval denominator', y)
    return times(x, (1/y[1], 1/y[0]))


def interval_power(x, n):
    out = exact(1)
    while n:
        if n & 1:
            out = times(out, x)
        x = times(x, x)
        n //= 2
    return out


def arctangent_reciprocal(q, terms=100):
    total = sum((F((-1)**j, (2*j+1)*q**(2*j+1)) for j in range(terms)), F(0))
    error = F(1, (2*terms+1)*q**(2*terms+1))
    return rounded(total-error, total+error)


def pi_interval():
    # Machin's identity; alternating-series error is rigorous.
    return minus(times(exact(16), arctangent_reciprocal(5)),
                 times(exact(4), arctangent_reciprocal(239)))


def sine_rational_pi(k, m, pi):
    # Absolute sine of k*pi/m, reduced to [0,pi/2].
    k %= 2*m
    if k > m:
        k = 2*m-k
    k = min(k, m-k)
    if k == 0:
        return exact(0)
    x = times(exact(F(k, m)), pi)
    x2 = times(x, x)
    term, total = x, exact(0)
    for j in range(40):
        total = plus(total, term if j % 2 == 0 else negative(term))
        term = divided(times(term, x2), exact((2*j+2)*(2*j+3)))
    # Taylor polynomial through degree79; Lagrange remainder through degree80.
    error = x[1]**81/F(factorial(81))
    return rounded(total[0]-error, total[1]+error)


def logarithm(x, terms=180):
    assert x[0] > 0
    t = divided(minus(x, exact(1)), plus(x, exact(1)))
    t2 = times(t, t)
    power, total = t, exact(0)
    for j in range(terms):
        total = plus(total, divided(power, exact(2*j+1)))
        power = times(power, t2)
    total = times(exact(2), total)
    bound = max(abs(t[0]), abs(t[1]))
    assert bound < 1
    error = 2*bound**(2*terms+1)/((2*terms+1)*(1-bound*bound))
    return rounded(total[0]-error, total[1]+error)


def determinant_interval(matrix):
    a = [row[:] for row in matrix]
    result = exact(1)
    for k in range(len(a)):
        pivot = next((i for i in range(k, len(a)) if a[i][k][0]*a[i][k][1] > 0), None)
        if pivot is None:
            return None
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            result = negative(result)
        v = a[k][k]
        result = times(result, v)
        for i in range(k+1, len(a)):
            factor = divided(a[i][k], v)
            for j in range(k+1, len(a)):
                a[i][j] = minus(a[i][j], times(factor, a[k][j]))
    return result


def display_interval(x, digits=12):
    denominator = 10**digits
    return {'lower_numerator': floorq(x[0]*denominator),
            'upper_numerator': ceilq(x[1]*denominator),
            'denominator': denominator}


def unit_certificate(m, exponents=None):
    embeddings = [k for k in range(1, (m+1)//2) if gcd(k, m) == 1]
    s = len(embeddings)
    assert s >= 2 and embeddings[0] == 1
    pi = pi_interval()
    candidates = exponents or [a for a in range(2, m//2+1) if gcd(a, m) == 1]
    magnitudes, logs = {}, {}
    for a in candidates:
        assert gcd(a, m) == 1
        magnitudes[a] = [divided(sine_rational_pi(a*k, m, pi),
                                sine_rational_pi(k, m, pi)) for k in embeddings]
        logs[a] = [logarithm(v) for v in magnitudes[a]]
    chosen, determinant = None, None
    for possible in itertools.combinations(candidates, s-1):
        matrix = [[logs[a][j] for a in possible] for j in range(s-1)]
        det = determinant_interval(matrix)
        if det is not None and det[0]*det[1] > 0:
            chosen, determinant = possible, det
            break
    if chosen is None:
        return {'conductor': m, 'status': 'no certified independent subset in this candidate list'}
    bounds = []
    for a in chosen:
        maximum = max(max(v[1], 1/v[0]) for v in magnitudes[a])
        bounds.append(ceilq(maximum))
    U = 1
    for b in bounds:
        U *= b
    return {'format': 'cyclotomic-independent-units-v1', 'conductor': m,
            'degree': 2*s, 'embedding_exponents': embeddings,
            'unit_geometric_sum_lengths': list(chosen),
            'unit_polynomials': [[1]*a for a in chosen],
            'embedding_and_reciprocal_integer_bounds': bounds,
            'subgroup_balance_product_U': U,
            'energy_bound_coefficient_sU': s*U,
            'log_minor_interval': display_interval(determinant),
            'rank': s-1, 'interval_bits': BITS,
            'proof': 'Each unit is (1-zeta^a)/(1-zeta), a coprime to m; the certified nonzero log minor proves independence. Full unit index is not asserted.'}


def nonprincipal_23():
    p = 23
    residues = {a*a % p for a in range(1, p)}
    tau = [0]+[1 if a in residues else -1 for a in range(1, p)]
    square = [sum(tau[j]*tau[(k-j) % p] for j in range(p)) for k in range(p)]
    reduced_square = [square[i]-square[-1] for i in range(p-1)]
    assert reduced_square == [-23]+[0]*21
    reduced_tau = [tau[i]-tau[-1] for i in range(p-1)]
    omega_twice = reduced_tau[:]
    omega_twice[0] += 1
    assert all(a % 2 == 0 for a in omega_twice)
    omega = [a//2 for a in omega_twice]
    # The reduced positive forms of discriminant -23 give the complete class group size.
    forms = []
    for a in range(1, 3):  # a <= sqrt(23/3) < 3
        for b in range(-a, a+1):
            if (b*b+23) % (4*a):
                continue
            c = (b*b+23)//(4*a)
            if a > c or (abs(b) == a or a == c) and b < 0:
                continue
            if gcd(gcd(a, abs(b)), c) != 1:
                continue
            forms.append([a, b, c])
    assert forms == [[1, 1, 6], [2, -1, 3], [2, 1, 3]]
    # N(a+b*omega) = a^2+a*b+6*b^2. No element has norm2;
    # for b!=0, completing the square gives norm >=23/4>2.
    assert 23 > 8
    assert all(a*a != 2 for a in range(-2, 3))
    assert 2*2+2*(-1)+6*(-1)**2 == 8
    order = next(k for k in range(1, 23) if pow(2, k, 23) == 1)
    assert order == 11 and gcd(11, 3) == 1
    return {'format': 'cyclotomic-nonprincipal-prime-v1', 'conductor': 23,
            'degree': 22, 'quadratic_subfield_discriminant': -23,
            'gauss_sum_square_reduced': reduced_square,
            'omega_coefficients': omega,
            'omega_equation': 'omega^2-omega+6=0',
            'quadratic_reduced_forms': forms, 'quadratic_class_number': 3,
            'quadratic_prime_ideal': '(2,omega)', 'quadratic_prime_class_order': 3,
            'cube_principal_generator_in_basis_1_omega': [2, -1],
            'relative_degree': 11, 'order_of_2_mod_23': order,
            'extended_prime_ideal_norm': 2**11,
            'conclusion': 'P=(2,omega)O_K is prime and nonprincipal: if principal, its relative ideal norm p^11 would be principal, contrary to class order3. Rational2 is irreducible but not prime in O_K.',
            'limitation': 'This certifies a nonprincipal prime and h_K divisible by3; it does not compute the full class number of K23.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--m', nargs='*', type=int, default=[7, 9, 11, 15, 16, 20, 24, 23])
    parser.add_argument('--output')
    args = parser.parse_args()
    result = {'unit_subgroups': [unit_certificate(m) for m in args.m],
              'nonprincipal_control': nonprincipal_23()}
    encoded = json.dumps(result, indent=2, sort_keys=True)+'\n'
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(encoded)
    else:
        print(encoded, end='')


if __name__ == '__main__':
    main()
