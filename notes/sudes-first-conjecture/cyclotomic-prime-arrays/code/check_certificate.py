#!/usr/bin/env python3
"""Independent exact cyclotomic-array checker, authored by /root/normalization.

Imports no producer code. Norms use a multiplication-matrix determinant;
normalization uses direct quadratic-surd coordinates, and irreducibility uses
exhaustive low-degree divisor tests. Certificates concern finite arrays only.
"""
import argparse
import copy
import glob
import itertools
import json
from math import isqrt
from pathlib import Path


class Invalid(ValueError):
    pass


def require(ok, message):
    if not ok:
        raise Invalid(message)


def element(value):
    require(isinstance(value, (tuple, list)) and len(value) == 4,
            'element must have four coefficients')
    require(all(type(x) is int for x in value), 'nonintegral coefficient')
    return tuple(value)


def qadd(x, y):
    return (x[0] + y[0], x[1] + y[1])


def qscale(c, x):
    return (c*x[0], c*x[1])


def qmul(x, y, d):
    return (x[0]*y[0] + d*x[1]*y[1], x[0]*y[1] + x[1]*y[0])


def qsign(x, d):
    """Exact sign of x[0]+x[1]*sqrt(d), no float evaluation."""
    a, b = x
    if b == 0:
        return 0 if a == 0 else (1 if a > 0 else -1)
    if a == 0:
        return 1 if b > 0 else -1
    if a >= 0 and b >= 0:
        return 1
    if a <= 0 and b <= 0:
        return -1
    square_comparison = a*a - d*b*b
    require(square_comparison != 0, 'unexpected rational square root')
    return (1 if square_comparison > 0 else -1) * (1 if a > 0 else -1)


def determinant(matrix):
    """Fraction-free Bareiss elimination over the integers."""
    a = [list(row) for row in matrix]
    n, sign, previous = len(a), 1, 1
    for k in range(n-1):
        if a[k][k] == 0:
            pivot = next((i for i in range(k+1, n) if a[i][k]), None)
            if pivot is None:
                return 0
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        v = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                numerator = a[i][j]*v - a[i][k]*a[k][j]
                require(numerator % previous == 0, 'Bareiss division failure')
                a[i][j] = numerator//previous
            a[i][k] = 0
        previous = v
    return sign*a[-1][-1]


def strip(poly, p):
    f = [c % p for c in poly]
    while f and f[-1] == 0:
        f.pop()
    return f


def polynomial_remainder(poly, divisor, p):
    f, g = strip(poly, p), strip(divisor, p)
    require(bool(g), 'zero polynomial divisor')
    inverse = pow(g[-1], p-2, p)
    while len(f) >= len(g):
        shift = len(f)-len(g)
        multiplier = f[-1]*inverse % p
        for i in range(len(g)):
            f[shift+i] = (f[shift+i]-multiplier*g[i]) % p
        f = strip(f, p)
    return f


def polynomial_gcd(a, b, p):
    a, b = strip(a, p), strip(b, p)
    while b:
        a, b = b, polynomial_remainder(a, b, p)
    require(bool(a), 'zero gcd')
    inverse = pow(a[-1], p-2, p)
    return [c*inverse % p for c in a]


def irreducible_small(f, p):
    """Any reducible polynomial of degree <=4 has a factor of degree <=2."""
    degree = len(f)-1
    if not 1 <= degree <= 4 or f[-1] != 1:
        return False
    for e in range(1, degree//2+1):
        for coefficients in itertools.product(range(p), repeat=e):
            divisor = list(coefficients) + [1]
            if not polynomial_remainder(f, divisor, p):
                return False
    return True


def is_rational_prime(p):
    if p < 2:
        return False
    return all(p % q for q in range(2, isqrt(p)+1))


def prime_power_factor(N):
    if N < 2:
        return None
    p = next((q for q in range(2, isqrt(N)+1) if N % q == 0), N)
    exponent, remainder = 0, N
    while remainder % p == 0:
        exponent += 1
        remainder //= p
    if remainder != 1:
        return None
    return p, exponent


class ExactField:
    def __init__(self, m):
        require(m in (5, 8, 12), 'unsupported conductor')
        self.m = m
        self.polynomial = {5:[1, 1, 1, 1, 1], 8:[1, 0, 0, 0, 1],
                           12:[1, 0, -1, 0, 1]}[m]
        self.radicand = {5:5, 8:2, 12:3}[m]
        self.omitted = {5:[5], 8:[2], 12:[2, 3]}[m]
        self.unit = {5:(0, 0, -1, -1), 8:(1, 1, 0, -1),
                     12:(1, 1, 0, 0)}[m]
        self.norm_cache = {}
        self.prime_cache = {}

    def times_x(self, a):
        last = a[3]
        return tuple((a[i-1] if i else 0) - last*self.polynomial[i]
                     for i in range(4))

    def multiplication_matrix(self, a):
        columns = [a]
        for _ in range(3):
            columns.append(self.times_x(columns[-1]))
        return [[columns[j][i] for j in range(4)] for i in range(4)]

    def multiply(self, a, b):
        mat = self.multiplication_matrix(a)
        return tuple(sum(mat[i][j]*b[j] for j in range(4)) for i in range(4))

    def norm(self, a):
        a = element(a)
        if a not in self.norm_cache:
            self.norm_cache[a] = determinant(self.multiplication_matrix(a))
            require(self.norm_cache[a] >= 0, 'negative totally imaginary norm')
        return self.norm_cache[a]

    def normalized(self, value):
        a0, a1, a2, a3 = element(value)
        d = self.radicand
        if self.m == 5:
            # X=4 Re(sigma_1(alpha)); V=2 Im(sigma_1(alpha))/sin(pi/5).
            X = (4*a0-a1-a2-a3, a1-a2-a3)
            V = (a1+2*a2-2*a3, a1)
            # Sixteen times the oriented areas against angles +/-pi/10.
            Y = qmul((0, 2), V, 5)
            W = qmul((-1, 1), X, 5)
            A = qadd(qscale(2, qmul(X, X, 5)),
                     qmul((5, -1), qmul(V, V, 5), 5))  # 32 |sigma_1|^2
            lambda_numerator, denominator = (3, 1), 2
        else:
            if self.m == 8:
                X, Y = (2*a0, a1-a3), (2*a2, a1+a3)
                tangent = (-1, 1)
                lambda_numerator = (3, 2)
            else:
                X, Y = (2*a0+a2, a1), (a1+2*a3, a2)
                tangent = (2, -1)
                lambda_numerator = (2, 1)
            W = qmul(tangent, X, d)
            A = qadd(qmul(X, X, d), qmul(Y, Y, d))  # 4 |sigma_1|^2
            denominator = 1
        if qsign(X, d) <= 0:
            return False
        if qsign(qadd(Y, W), d) < 0 or qsign(qadd(Y, qscale(-1, W)), d) >= 0:
            return False
        B = (A[0], -A[1])
        lower = qadd(qmul(A, lambda_numerator, d), qscale(-denominator, B))
        upper = qadd(qscale(denominator, A), qscale(-1, qmul(B, lambda_numerator, d)))
        return qsign(lower, d) >= 0 and qsign(upper, d) < 0

    def prime_record(self, value):
        a = element(value)
        if a in self.prime_cache:
            return self.prime_cache[a]
        N = self.norm(a)
        pe = prime_power_factor(N)
        answer = None
        if pe is not None:
            p, e = pe
            if e <= 4:
                g = polynomial_gcd(self.polynomial, a, p)
                if len(g) == e+1 and irreducible_small(g, p):
                    answer = {'norm': N, 'rational_prime': p,
                              'residue_degree': e, 'quotient_polynomial': g}
        self.prime_cache[a] = answer
        return answer

    def ideal_count(self, B):
        count = 0
        for p in range(2, B+1):
            if self.m % p == 0 or not is_rational_prime(p):
                continue
            degree = next(e for e in (1, 2, 4) if pow(p, e, self.m) == 1)
            if p**degree <= B:
                count += 4//degree
        return count


def all_lines(n, D):
    """Enumerate per-coordinate constants/forward/reverse maps, then deduplicate."""
    cells = list(itertools.product(range(n), repeat=D))
    index = {point: i for i, point in enumerate(cells)}
    possibilities = list(range(n)) + ['f', 'r']
    sets = set()
    for pattern in itertools.product(possibilities, repeat=D):
        if all(type(x) is int for x in pattern):
            continue
        current = []
        for t in range(n):
            point = tuple(t if p == 'f' else n-1-t if p == 'r' else p
                          for p in pattern)
            current.append(index[point])
        sets.add(tuple(sorted(current)))
    return sorted(sets)


def check(data):
    require(isinstance(data, dict), 'certificate is not an object')
    require(data.get('format') == 'cyclotomic-prime-array-v1', 'wrong format')
    f = ExactField(data['conductor'])
    n, D = data['side'], data['dimension']
    require(type(n) is int and n >= 1 and D in (2, 3), 'bad array dimensions')
    require(data['polynomial'] == f.polynomial, 'wrong defining polynomial')
    require(data['normalization'] == 'balanced-log-symmetric-sector-v1', 'wrong normalization')
    require(data['omitted_rational_primes'] == f.omitted, 'wrong ramified omissions')
    pool = [element(a) for a in data['pool']]
    require(len(pool) == n**D and len(set(pool)) == len(pool), 'wrong pool size or duplicate')
    comp = data['pool_completeness']
    B, H = comp['norm_cutoff'], comp['coefficient_scan_radius']
    require(type(B) is int and B > 1 and type(H) is int and H >= 1, 'bad completeness bounds')
    complete = [element(a) for a in comp['all_through_cutoff']]
    require(bool(complete), 'empty norm cutoff')
    ideal_keys = []
    for a in complete:
        require(max(map(abs, a)) <= H, 'entry outside claimed coefficient scan')
        require(f.normalized(a), 'noncanonical associate in complete prefix')
        rec = f.prime_record(a)
        require(rec is not None, 'nonprime element in complete prefix')
        require(rec['rational_prime'] not in f.omitted, 'ramified class retained')
        require(rec['norm'] <= B, 'entry past norm cutoff')
        ideal_keys.append((rec['rational_prime'], tuple(rec['quotient_polynomial'])))
    require(len(set(ideal_keys)) == len(ideal_keys), 'duplicate prime ideal/associate')
    expected_count = f.ideal_count(B)
    require(len(complete) == expected_count == comp['complete_tie_count'],
            'omitted or extra prime ideal before cutoff')
    complete = sorted(complete, key=lambda a: (f.norm(a), a))
    require([list(a) for a in complete] == comp['all_through_cutoff'],
            'complete prefix has wrong norm/lex ordering')
    require(pool == complete[:n**D], 'wrong prescribed initial pool')
    require(f.norm(pool[-1]) == B, 'cutoff is not last prescribed norm')
    arrangement = [element(a) for a in data['arrangement']]
    require(sorted(arrangement) == sorted(pool), 'array is not a bijection of exact pool')
    lines = all_lines(n, D)
    expected_lines = 1 if n == 1 else 2*n+2 if D == 2 else 3*n*n+6*n+4
    require(len(lines) == expected_lines, 'checker line count failure')
    require(len(data['lines']) == len(lines), 'missing or duplicate required line')
    seen = set()
    for record in data['lines']:
        line = tuple(record['cells'])
        require(line in lines and line not in seen, 'unrequired or repeated line')
        seen.add(line)
        total = tuple(sum(arrangement[i][j] for i in line) for j in range(4))
        require(element(record['sum']) == total, 'incorrect ordinary line sum')
        rec = f.prime_record(total)
        require(rec is not None, 'line sum is zero, unit, or composite')
        require(record['prime'] == rec, 'wrong prime ideal/residue certificate')
    require(seen == set(lines), 'missing signed-coordinate line')
    return {'conductor': f.m, 'dimension': D, 'side': n,
            'pool_size': len(pool), 'required_lines': len(lines),
            'norm_cutoff': B, 'all_prime_ideals_through_cutoff': expected_count}


def rejected(data):
    try:
        check(data)
    except (Invalid, KeyError, TypeError, IndexError):
        return True
    return False


def negative_controls(data):
    """Each mutation must fail; arithmetic controls include non-prime norms."""
    mutations = []
    def alter(name, function):
        candidate = copy.deepcopy(data)
        function(candidate)
        mutations.append((name, candidate))
    def varied_coordinates(record):
        coordinates = []
        for index in record['cells']:
            point = []
            for _ in range(data['dimension']):
                point.append(index % data['side'])
                index //= data['side']
            coordinates.append(point)
        return sum(len({point[j] for point in coordinates}) > 1
                   for j in range(data['dimension']))
    diagonal = next((i for i, record in enumerate(data['lines'])
                     if varied_coordinates(record) >= 2), 0)
    alter('missing diagonal', lambda c: c['lines'].pop(diagonal))
    alter('incorrect line sum', lambda c: c['lines'][0]['sum'].__setitem__(0, c['lines'][0]['sum'][0]+1))
    alter('wrong finite-field residue', lambda c: c['lines'][0]['prime'].__setitem__('quotient_polynomial', [0, 1]))
    alter('omitted prime class', lambda c: c['pool_completeness']['all_through_cutoff'].pop())
    alter('hidden extra ramified omission', lambda c: c['omitted_rational_primes'].append(7))
    alter('wrong prime rational norm', lambda c: c['lines'][0]['prime'].__setitem__('norm', c['lines'][0]['prime']['norm']+1))
    alter('prime-norm-only certificate', lambda c: c['lines'][0]['prime'].pop('residue_degree'))
    f = ExactField(data['conductor'])
    alter('hidden unit rescaling', lambda c: c['arrangement'].__setitem__(0, list(f.multiply(element(c['arrangement'][0]), f.unit))))
    if len(data['arrangement']) > 1:
        alter('repeated entry', lambda c: c['arrangement'].__setitem__(1, c['arrangement'][0][:]))
        alter('wrong initial-pool order', lambda c: c['pool'].__setitem__(slice(0, 2), c['pool'][1::-1]))
    for name, candidate in mutations:
        require(rejected(candidate), 'negative control accepted: '+name)
    # A rational-prime norm is not a necessary condition for a prime element.
    f5, f8 = ExactField(5), ExactField(8)
    require(f5.norm((2, 0, 0, 0)) == 16 and f5.prime_record((2, 0, 0, 0)) is not None,
            'inert prime element with composite norm was rejected')
    require(f8.norm((3, 0, 0, 0)) == 81 and f8.prime_record((3, 0, 0, 0)) is None,
            'split rational composite was accepted')
    for m in (5, 8, 12):
        field = ExactField(m)
        require(field.prime_record((0, 0, 0, 0)) is None, 'zero accepted')
        require(field.prime_record((1, 0, 0, 0)) is None, 'one accepted')
        require(field.prime_record(field.unit) is None, 'infinite-order unit accepted')
    return len(mutations), 11


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--negative-controls', action='store_true')
    parser.add_argument('inputs', nargs='+')
    args = parser.parse_args()
    paths = []
    for pattern in args.inputs:
        matches = sorted(glob.glob(pattern))
        require(bool(matches), 'no inputs match '+pattern)
        paths.extend(matches)
    total_controls = 0
    for path in paths:
        data = json.loads(Path(path).read_text())
        result = check(data)
        if args.negative_controls:
            mutations, arithmetic = negative_controls(data)
            result.update(rejected_mutations=mutations, arithmetic_controls=arithmetic)
            total_controls += mutations
        print(json.dumps({'input': path, **result}, sort_keys=True))
    print(json.dumps({'verified_files': len(paths), 'rejected_mutations': total_controls}))


if __name__ == '__main__':
    main()
