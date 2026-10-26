#!/usr/bin/env python3
"""Exact component regressions for the packed two-level folded compiler.
These finite tests are NOT a formal verification of the asymptotic reduction.
Run: python3 check_packed_two_level_fold.py [--output certificate.json]
Only the Python standard library is required.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from fractions import Fraction
from pathlib import Path


class BinaryField:
    def __init__(self, degree: int, modulus: int):
        self.degree, self.modulus = degree, modulus
        self.size = 1 << degree

    def mul(self, a: int, b: int) -> int:
        ans = 0
        while b:
            if b & 1:
                ans ^= a
            b >>= 1
            a <<= 1
            if a & self.size:
                a ^= self.modulus
        return ans

    def pow(self, a: int, n: int) -> int:
        ans = 1
        while n:
            if n & 1:
                ans = self.mul(ans, a)
            a = self.mul(a, a)
            n >>= 1
        return ans

    def inv(self, a: int) -> int:
        if not a:
            raise ZeroDivisionError
        return self.pow(a, self.size - 2)


class Quad:
    """F[z]/(z^2+z+c), natural bitwise embedding of F."""
    def __init__(self, base):
        self.base = base
        self.degree = 2 * base.degree
        self.size = 1 << self.degree
        self.mask = base.size - 1
        self.z = base.size
        for i in range(base.degree):
            c, tr, x = 1 << i, 0, 1 << i
            for _ in range(base.degree):
                tr ^= x
                x = base.mul(x, x)
            if tr == 1:
                self.c = c
                break
        else:
            raise AssertionError('No trace-one basis element')

    def mul(self, x: int, y: int) -> int:
        a, b = x & self.mask, x >> self.base.degree
        c, d = y & self.mask, y >> self.base.degree
        bd = self.base.mul(b, d)
        lo = self.base.mul(a, c) ^ self.base.mul(self.c, bd)
        hi = self.base.mul(a, d) ^ self.base.mul(b, c) ^ bd
        return lo | (hi << self.base.degree)

    pow = BinaryField.pow
    inv = BinaryField.inv


def rank2(v, field):
    if not any(v):
        return 0
    return 2 if field.mul(v[0], v[3]) ^ field.mul(v[1], v[2]) else 1


def two_level_rank_test():
    # F_2 < F_4 < F_16, degrees d_inner=d_outer=1.
    F = BinaryField(1, 3)
    H, E = Quad(F), None
    E = Quad(H)
    local_table = {}
    for values in itertools.product(range(4), repeat=4):
        local_table[values] = sum(rank2(tuple(
            (x & 1) ^ ((x >> 1) & t) for x in values), F)
            for t in range(2))
    checked, equality, minimum_slack = 0, 0, 100
    for coeff in itertools.product(range(4), repeat=8):
        A, B = coeff[:4], coeff[4:]
        global_rank = rank2(tuple(A[i] ^ E.mul(B[i], E.z)
                                 for i in range(4)), E)
        charge = 0
        for zeta in range(4):
            values = tuple(A[i] ^ H.mul(zeta, B[i]) for i in range(4))
            charge += local_table[values]
        slack = charge - 3 * global_rank  # (2-1)(4-1)=3
        assert slack >= 0, (coeff, charge, global_rank)
        checked += 1
        equality += slack == 0
        minimum_slack = min(minimum_slack, slack)
    return dict(cases=checked, equality_cases=equality,
                minimum_slack=minimum_slack, fields=[2, 4, 16])


class Cubic:
    """F_4[z]/(z^3+z+1); irreducible since no root lies in F_4."""
    def __init__(self, base):
        self.base, self.degree, self.size = base, 6, 64
        self.z = 4
        assert all(base.pow(x, 3) ^ x ^ 1 for x in range(4))

    def mul(self, a, b):
        aa, bb = [(a >> (2*i)) & 3 for i in range(3)], [(b >> (2*i)) & 3 for i in range(3)]
        v = [0] * 5
        for i in range(3):
            for j in range(3):
                v[i+j] ^= self.base.mul(aa[i], bb[j])
        for k in (4, 3):
            v[k-3] ^= v[k]
            v[k-2] ^= v[k]
        return sum(v[i] << (2*i) for i in range(3))

    pow = BinaryField.pow
    inv = BinaryField.inv


def packed_source_test():
    B = BinaryField(2, 7)
    E = Cubic(B)
    # Exhaust all columns in B^4 for every possible tag in E.
    columns = 0
    for alpha in range(64):
        coordinates = [(alpha >> (2*i)) & 3 for i in range(3)]
        for column in itertools.product(range(4), repeat=4):
            rhs = column[1] | (column[2] << 2) | (column[3] << 4)
            valid = E.mul(alpha, column[0]) == rhs
            expected = all(column[i+1] == B.mul(coordinates[i], column[0])
                           for i in range(3))
            assert valid == expected
            columns += 1
    # T encodes two Boolean bits; A=x0, Bv=x1; P=A*Bv.
    # UNSAT: A=x0, Bv=x1, P=1, x0=0. SAT: omit x0=0.
    signatures_no, signatures_yes = [], []
    valid_yes = []
    for alpha in range(64):
        T, A, Bv = [(alpha >> (2*i)) & 3 for i in range(3)]
        x0, x1 = T & 1, T >> 1
        defects = (A ^ x0, Bv ^ x1, B.mul(A, Bv) ^ 1, x0)
        sig_no, sig_yes, shift = 0, 0, 0
        for e in range(4):
            power = E.pow(alpha, e)
            for j, d in enumerate(defects):
                value = E.mul(power, d)
                sig_no |= value << shift
                if j < 3:
                    sig_yes |= value << shift
                shift += 6
        signatures_no.append(sig_no)
        signatures_yes.append(sig_yes)
        if sig_yes == 0:
            valid_yes.append(alpha)
    assert len(valid_yes) == 1
    populations = 0
    for size in (1, 3):
        for support in itertools.combinations(range(64), size):
            sig = 0
            for alpha in support:
                sig ^= signatures_no[alpha]
            assert sig != 0, support
            populations += 1
    return dict(exhaustive_column_cases=columns,
                unsat_odd_atomic_populations_checked=populations,
                sat_singleton_tags=valid_yes)


def lagrange_weights(points, target, field):
    ans = []
    for j, xj in enumerate(points):
        num = den = 1
        for k, xk in enumerate(points):
            if k != j:
                num = field.mul(num, target ^ xk)
                den = field.mul(den, xj ^ xk)
        ans.append(field.mul(num, field.inv(den)))
    return ans


def eval_poly(coeff, x, field):
    ans = 0
    for a in reversed(coeff):
        ans = field.mul(ans, x) ^ a
    return ans


def generalized_interpolation_test():
    # Exercise inner degree h-1=3 rather than the old quadratic case.
    F = BinaryField(4, 0b10011)
    H = Quad(Quad(F))  # F_16 < F_(16^4)
    omega = H.z
    basis = [H.pow(omega, j) for j in range(4)]
    points = list(range(10))  # Delta=3, Delta*(h-1)+1=10
    weights = lagrange_weights(points, omega, H)
    cases = 0
    # All basis triples prove the trilinear identity on H over F;
    # shorter arities explicitly check padding by one.
    for arity in range(4):
        for indices in itertools.product(range(4), repeat=arity):
            expected = 1
            for j in indices:
                expected = H.mul(expected, basis[j])
            result = 0
            for t, weight in zip(points, weights):
                v = 1
                for j in indices:
                    v = F.mul(v, F.pow(t, j))
                result ^= H.mul(weight, v)
            assert result == expected, indices
            cases += 1
    return dict(intermediate_degree=4, arity=3,
                multilinear_basis_and_padding_cases=cases,
                base_cardinality=16, intermediate_cardinality=H.size)


def next_power_two(x):
    return 1 << (x - 1).bit_length()


def schedule_test():
    rows = []
    for denominator in (3, 4, 10, 100, 1000):
        eps = Fraction(1, denominator)
        h = next_power_two(1 + 4 * denominator)
        threshold = Fraction(3*h-1, 2) / eps - 2*h
        r = threshold.numerator // threshold.denominator + 1
        p = Fraction(r + 2*h, h-1)
        c = Fraction(r-h+1, 2*(r+2*h))
        assert c > Fraction(1, 2) - eps
        assert p < Fraction(3, 2)/eps + 1
        rows.append(dict(epsilon=str(eps), h=h, r=r,
                         rank_exponent_infimum=str(p), hardness_frontier=str(c),
                         clean_rank_degree_bound=str(Fraction(3, 2)/eps+1)))
    # Exact inequalities for the field schedule, including small N.
    checks = 0
    for N in (8, 9, 16, 31, 100, 1000):
        for h in (2, 4, 8, 16):
            s = 2
            while s**(h-1) < N:
                s *= 2
            ell = next_power_two(2*N)
            for r in (h, 2*h, 5*h):
                delta = (2*r+4)*s
                q = next_power_two(16*h*delta)
                n = 4*h*ell
                di, do = (h-1)*delta, (n-1)*delta
                assert 2*di <= q and 2*do <= q**h
                checks += 1
    return dict(rows=rows, field_schedule_cases=checks)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = dict(
        schema='cvp.packed-two-level-fold.v1',
        scope='Finite component regressions; not a Lean proof or full asymptotic compiler verification.',
        two_level_rank=two_level_rank_test(),
        packed_source=packed_source_test(),
        generalized_interpolation=generalized_interpolation_test(),
        schedules=schedule_test())
    payload = json.dumps(report, sort_keys=True, separators=(',', ':')).encode()
    report['sha256_without_hash'] = hashlib.sha256(payload).hexdigest()
    text = json.dumps(report, sort_keys=True, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text)


if __name__ == '__main__':
    main()
