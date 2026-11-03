#!/usr/bin/env python3
"""Independent finite controls for FC/FP at c5cf3d829f83dcc3.

Reviewer: /root/physical_composition_review, 2026-11-03.
No author implementation is imported.  These checks bind source bytes and
test finite signatures, actual local swaps, compatible splitting, packing
and rational resource calculations.  They do not prove the asymptotic
packing theorem, UF, AF, or certify a complete higher-dimensional array.

Python >=3.11, standard library only.  Example:
  python3 -B reviews/hyperk_full_composition_controls.py \
      --source-root /path/to/exact/archive/problems/prime-arrays-beyond-square
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
import hashlib
from itertools import combinations, permutations, product
import json
from math import comb
from pathlib import Path
import random


REVISION = "c5cf3d829f83dcc388af6f065d7f9bda66789458"
TREE = "faf629e6c7357585720385a36e9a0b3aaf28fb49"
PREVIOUS_REVISION = "c7f22dd8a01d28ab02c832f6c2b8b4145d88b6bb"
BINDINGS = {
    "manuscripts/hyperk_full.md": "6c0a5c68259154745edf1bfc459437b9b1744c6eeb4f9df0c184c335367dc721",
    "code/hyperk_full.py": "637c0274697ef0590fe030d3f4714df38026d95075f23854ae892be85af0bec5",
    "manuscripts/hyperk_distributed_kernel.md": "a0ea6e14b51b2cdd92b4c9da442f1fef3eeeafa26cf3ef3f84dd4290f9c6ac27",
    "code/hyperk_distributed_kernel.py": "b05dc1078ba84f7969898abd6d6444249b12d953df0a8fd7316abae0e2535e8a",
    "manuscripts/hyperk_full_controller.md": "38de54de8b5e5d751e9d700f689b9417b610019d56e170d47f209c86e2adbec6",
    "manuscripts/hyperk_reconstruction_alt.md": "623cae1101615723a9ddc367145675c41d93067ee64502663b56d072059eeeb5",
    "manuscripts/hyperk_incidence.md": "fd2ab35b539415ac65a132b7fddfb6acaa87b5af65f579f9eb64f27cc7e403d8",
    "manuscripts/hyperk_controller.md": "bcccf122f966daf70101bfff1f4cf00cfc9559c68c5097d80c981ae405cf1f23",
    "manuscripts/hyperk_resources.md": "c26bd5d67dd3dee746c986c1d11695a4ba92d2aeda53f0e5441b1adf113ce0a7",
    "manuscripts/hyperk_targets.md": "2a69a31ce1a3ecde164bf7748dc52c22b2637551bc97dd821edd497ea9df5306",
    "manuscripts/hyperk_kernel_research.md": "c4dc2db4da2e502f0bc8d564e44c2f504b13e9e0fae7ae77b780cfdb70838f44",
}
PREVIOUS_BINDINGS = BINDINGS | {
    "manuscripts/hyperk_full.md": "d6c09eea509ae7cb288d87705efdaf4ad4530bed4501ed135135787c20e78da9",
    "code/hyperk_full.py": "22d774bd31f335b8668421db6f0334a4acc72826d19cb8c612572728ab1b401c",
}


def check_bindings(root, bindings=BINDINGS):
    for name, expected in bindings.items():
        got = hashlib.sha256((root / name).read_bytes()).hexdigest()
        assert got == expected, ("wrong source bytes", name, got, expected)
    return len(bindings)


def sparse(values):
    return {x: a for x, a in values.items() if a}


def sum_tensors(*terms):
    out = defaultdict(int)
    for scale, values in terms:
        for x, a in values.items():
            out[x] += scale * a
    return sparse(out)


def put_product(k, factors):
    out = {(): 1}
    coordinates = []
    for axes, values in factors:
        out = {x + y: a * b for x, a in out.items() for y, b in values.items()}
        coordinates.extend(axes)
    assert sorted(coordinates) == list(range(k))
    order = [coordinates.index(i) for i in range(k)]
    return {tuple(x[i] for i in order): a for x, a in out.items()}


@lru_cache(None)
def signed_blocks(k):
    return tuple((axes, (1,) + signs)
                 for r in range(1, k + 1)
                 for axes in combinations(range(k), r)
                 for signs in product((-1, 1), repeat=r - 1))


@lru_cache(None)
def signed_partitions(k):
    """Enumerate disjoint subsets of the independently enumerated block list."""
    options = [(h, sum(1 << i for i in h[0]))
               for h in signed_blocks(k) if len(h[0]) >= 2]
    out = []

    def visit(start, mask, picked):
        out.append(tuple(picked))
        for j in range(start, len(options)):
            h, bits = options[j]
            if not bits & mask:
                visit(j + 1, mask | bits, picked + [h])

    visit(0, 0, [])
    assert len(out) == len(set(out))
    return tuple(out)


def contraction(tensor, k, partition):
    used = {i for axes, _ in partition for i in axes}
    keep = [i for i in range(k) if i not in used]
    out = defaultdict(int)
    for x, a in tensor.items():
        # Direct coordinate equations, with no precomputed incidence matrix.
        if all(len({sign * x[i] for i, sign in zip(axes, signs)}) == 1
               for axes, signs in partition):
            out[tuple(x[i] for i in keep)] += a
    return sparse(out)


def is_kernel(values, k, modulus=None):
    return all(all(a % modulus == 0 for a in contraction(values, k, (h,)).values())
               if modulus else not contraction(values, k, (h,))
               for h in signed_blocks(k))


def unsigned_proper_partitions(r):
    return [tuple(h[0] for h in p) for p in signed_partitions(r)
            if all(len(h[0]) < r and all(s == 1 for s in h[1]) for h in p)]


@lru_cache(None)
def pure(r):
    """Independent PS inclusion/exclusion construction on positive labels."""
    assert r >= 2
    coordinate_factors = [{(1,): 1, (i + 2,): -1} for i in range(r)]
    cursor = r + 2
    copies = {}
    for size in range(2, r):
        for axes in combinations(range(r), size):
            base, alphabet = pure(size)
            copies[axes] = {tuple(cursor + t - 1 for t in x): a
                            for x, a in base.items()}
            cursor += alphabet
    answer = {}
    for p in unsigned_proper_partitions(r):
        used = {i for axes in p for i in axes}
        factors = [(axes, copies[axes]) for axes in p]
        factors.extend(((i,), coordinate_factors[i]) for i in range(r) if i not in used)
        piece = put_product(r, factors)
        assert not answer.keys() & piece.keys(), "PS pieces overlap"
        answer = sum_tensors((1, answer), ((-1) ** len(p), piece))
    return answer, cursor - 1


def reflected_selector(axes, signs, labels):
    q, count = pure(len(axes))
    assert len(labels) == count and len(set(labels)) == count
    return {tuple(s * labels[t - 1] for s, t in zip(signs, x)): a
            for x, a in q.items()}


def generic_kernel(d, offset=0, shifted=0):
    # The first factor may meet the center.  Distinct coordinate factors have
    # disjoint absolute alphabets, so every larger contraction vanishes.
    factors = []
    for i in range(d):
        a, b = offset + 10 * i, offset + 10 * i + 1 + (shifted if i == 0 else 0)
        factors.append(((i,), {(a,): 1, (b,): -1}))
    return put_product(d, factors)


def native_stage(k, partition, inner=None, start=100):
    used = {i for h, _ in partition for i in h}
    free = tuple(i for i in range(k) if i not in used)
    if inner is None:
        inner = generic_kernel(len(free))
    native_alphabet = {abs(t) for x in inner for t in x}
    factors = []
    for axes, signs in partition:
        _, count = pure(len(axes))
        while any(t in native_alphabet for t in range(start, start + count)):
            start += count + 1
        q = reflected_selector(axes, signs, tuple(range(start, start + count)))
        factors.append((axes, q))
        start += count + 11
    factors.append((free, inner))
    return put_product(k, factors), factors, inner


def check_signature(k, partition, values, factors, exhaustive=True):
    native = set(partition)
    for h in signed_blocks(k):
        got = contraction(values, k, (h,))
        if h not in native:
            assert not got, ("unintended line family", k, partition, h)
    rho_list = signed_partitions(k) if exhaustive else [tuple(p)
        for size in range(len(partition) + 1) for p in combinations(partition, size)]
    for rho in rho_list:
        got = contraction(values, k, rho)
        if not set(rho) <= native:
            assert not got, ("unintended shared trace", k, partition, rho)
            continue
        removed = {i for axes, _ in rho for i in axes}
        keep = [i for i in range(k) if i not in removed]
        expected_factors = [(tuple(keep.index(i) for i in axes), t)
                            for axes, t in factors if not axes or not set(axes) <= removed]
        expected = put_product(len(keep), expected_factors)
        assert got == expected, ("wrong surviving partition image", k, partition, rho)


def point_line_keys(x):
    """Derive incident lines from reflection classes, independently of contraction."""
    k = len(x)
    groups = defaultdict(list)
    for i, a in enumerate(x):
        groups[abs(a)].append(i)
    for absolute, coordinates in groups.items():
        for r in range(1, len(coordinates) + 1):
            for axes in combinations(coordinates, r):
                if absolute == 0:
                    patterns = ((1,) + t for t in product((-1, 1), repeat=r - 1))
                else:
                    patterns = [tuple(a // x[axes[0]] for a in (x[i] for i in axes))]
                fixed = tuple(x[i] for i in range(k) if i not in axes)
                for signs in patterns:
                    yield axes, signs, fixed


def geometry_check(k, n):
    domain = range(-(n // 2), n // 2 + 1)
    produced = {}
    for h in signed_blocks(k):
        axes, signs = h
        keep = [i for i in range(k) if i not in axes]
        for c in product(domain, repeat=len(keep)):
            cells = []
            for t in domain:
                x = [None] * k
                for i, a in zip(keep, c):
                    x[i] = a
                for i, s in zip(axes, signs):
                    x[i] = s * t
                cells.append(tuple(x))
            produced[(axes, signs, c)] = frozenset(cells)
    discovered = defaultdict(set)
    for x in product(domain, repeat=k):
        for key in point_line_keys(x):
            discovered[key].add(x)
    assert produced == discovered
    assert len(set(produced.values())) == len(produced)
    expected = ((n + 2) ** k - n ** k) // 2
    assert len(produced) == expected
    return {"k": k, "n": n, "lines": expected}


def prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def validate_trade(values, before, after, gap):
    assert set(before) == set(after) == set(values)
    assert len(set(before.values())) == len(before)
    assert Counter(before.values()) == Counter(after.values())
    assert all(prime(p) for p in before.values())
    assert all(after[x] - before[x] == gap * values[x] for x in values)


def actual_trade(values, gap, used=None):
    assert set(values.values()) <= {-1, 1}
    fibers = defaultdict(lambda: [[], []])
    for x, a in values.items():
        fibers[x[1:]][0 if a > 0 else 1].append(x)
    before, after = {}, {}
    used = set() if used is None else used
    candidate = 3
    for positive, negative in fibers.values():
        assert len(positive) == len(negative)
        for x, y in zip(sorted(positive), sorted(negative)):
            while (candidate in used or candidate + gap in used
                   or not prime(candidate) or not prime(candidate + gap)):
                candidate += 2
            before[x], before[y] = candidate, candidate + gap
            after[x], after[y] = candidate + gap, candidate
            used.update((candidate, candidate + gap))
            candidate += 2
    validate_trade(values, before, after, gap)
    return before, after


def complete_bundle_checks():
    """Two legal complementary center states, plus an exact unused-mean audit."""
    ranges = []
    for k, p in [(2, (((0, 1), (1, -1)),)),
                 (4, (((0, 1), (1, 1)), ((2, 3), (1, -1))))]:
        shared_endpoints = set()
        state_a, state_b = {}, {}
        stage_hits = Counter()
        for j, gap in enumerate((6, 12, 18, 24)):
            factors = []
            for h, (axes, signs) in enumerate(p):
                start = 1 + 3 * (j * len(p) + h)
                factors.append((axes, reflected_selector(axes, signs, (start, start + 1, start + 2))))
            t = put_product(k, factors)
            before, after = actual_trade(t, gap, shared_endpoints)
            assert not state_a.keys() & t.keys()
            state_a.update(after if j in (0, 3) else before)
            state_b.update(before if j in (0, 3) else after)
            stage_hits.update(set(key for x in t for key in point_line_keys(x)))
        assert len(set(state_a.values())) == len(state_a)
        assert Counter(state_a.values()) == Counter(state_b.values())
        delta = sum_tensors((1, state_b), (-1, state_a))
        by_line = Counter()
        for x, a in delta.items():
            for key in point_line_keys(x):
                by_line[key] += a
        bound = max(abs(a) for a in by_line.values())
        assert bound <= (4 ** len(p)) * max(state_a.values())
        for (axes, signs, _), hits in stage_hits.items():
            if len(p) >= 2 or (axes, signs) != p[0]:
                assert hits <= 1
        if len(p) == 1:
            assert not contraction(delta, k, p)
        ranges.append({"k": k, "stages": 4, "fresh_prime_endpoints": len(state_a),
                       "central_scalar_totals": [30, 30], "maximum_line_change": bound})
        if k == 2:
            # All displayed labels fit I_25.  This is an exact-pool permutation
            # control, expressly not an all-prime-line arrangement certificate.
            n = 25
            pool = []
            trial = 3
            while len(pool) < n*n:
                if prime(trial):
                    pool.append(trial)
                trial += 2
            assert set(state_a.values()) <= set(pool)
            unused = [x for x in pool if x not in state_a.values()]
            mean = Fraction(sum(pool), n*n)
            reserved_sums = Counter()
            reserved_counts = Counter()
            for x, value in state_a.items():
                for key in point_line_keys(x):
                    reserved_sums[key] += value
                    reserved_counts[key] += 1
            E = max(abs(reserved_sums[key] - count*mean)
                    for key, count in reserved_counts.items())
            unused_mean = Fraction(sum(unused), len(unused))
            assert unused_mean - mean == -(sum(state_a.values()) - len(state_a)*mean) / len(unused)
            assert abs(unused_mean - mean) <= Fraction(n, len(unused))*E <= 2*E/n
            complete = dict(state_a)
            free_cells = [x for x in product(range(-12, 13), repeat=2) if x not in complete]
            complete.update(zip(free_cells, unused))
            assert len(complete) == n*n and Counter(complete.values()) == Counter(pool)
            line_sums = Counter()
            for x, value in complete.items():
                line_sums.update({key: value for key in point_line_keys(x)})
            assert not all(prime(value) for value in line_sums.values())
    return ranges


def nearest(x):
    return (2 * x.numerator + x.denominator) // (2 * x.denominator)


def split_check(d, q):
    templates = [generic_kernel(d, shifted=j) for j in (0, 1, 2)]
    coefficients = [137, -211, 89]
    total = sum_tensors(*zip(coefficients, templates))
    degree = max(Counter(x for t in templates for x in t).values())
    previous = {}
    pieces = []
    for j in range(1, q + 1):
        current = sum_tensors(*[(nearest(Fraction(j * a, q)), t)
                               for a, t in zip(coefficients, templates)])
        piece = sum_tensors((1, current), (-1, previous))
        assert is_kernel(piece, d)
        assert max(map(abs, piece.values()), default=0) <= Fraction(max(map(abs, total.values())), q) + degree
        pieces.append(piece)
        previous = current
    assert sum_tensors(*[(1, t) for t in pieces]) == total
    return degree


def hierarchy_check(k, modulus=None):
    fixtures = [(((0, 1), (1, -1)),),
                (((0, 1), (1, -1)), ((2, 3), (1, 1))),
                (((0, 1, 2), (1, 1, -1)),)]
    if k == 6:
        fixtures.append((((0, 1), (1, 1)), ((2, 3), (1, -1)), ((4, 5), (1, 1))))
    original = {}
    for i, p in enumerate(fixtures):
        v, _, _ = native_stage(k, p, start=1000 + 100 * i)
        original = sum_tensors((1, original), ((-1) ** i * (13 + i), v))
    current = original
    levels = sorted((p for p in signed_partitions(k) if p), key=lambda p: -len(p))
    corrected = []
    checked_native = 0
    for p in levels:
        residual = contraction(current, k, p)
        if modulus:
            residual = sparse({x: a % modulus for x, a in residual.items()})
        free = k - sum(len(h[0]) for h in p)
        assert is_kernel(residual, free, modulus), ("F5 failed", p)
        if residual:
            step, factors, _ = native_stage(k, p, residual, start=10000 + 200 * checked_native)
            # Algebraic hierarchy control only: residual may have nonunit values.
            current = sum_tensors((1, current), (-1, step))
            if modulus:
                current = sparse({x: a % modulus for x, a in current.items()})
            checked_native += 1
            for old in corrected:
                old_image = contraction(current, k, old)
                assert all(a % modulus == 0 for a in old_image.values()) if modulus else not old_image
        corrected.append(p)
    assert is_kernel(current, k, modulus)
    return checked_native


def exact_packing_probabilities():
    """Exhaustive finite injection distribution, before/after collision rejection."""
    p = (((0, 1), (1, 1)), ((2, 3), (1, 1)))
    def support(labels):
        factors = [(axes, reflected_selector(axes, signs, labels[3 * j:3 * j + 3]))
                   for j, (axes, signs) in enumerate(p)]
        return set(put_product(4, factors))
    old = support((1, 2, 3, 4, 5, 6))
    total = legal = whole = proper = whole_legal = proper_legal = 0
    for labels in permutations(range(1, 9), 6):
        new = support(labels)
        ok = not old & new
        a = any(x[2:] == (4, 4) for x in new)
        b = any(x[1:] == (1, 4, 4) for x in new)
        total += 1
        legal += ok
        whole += a
        proper += b
        whole_legal += ok and a
        proper_legal += ok and b
    assert Fraction(legal, total) > Fraction(1, 2)
    assert Fraction(whole, total) == Fraction(1, 8)
    assert Fraction(proper, total) == Fraction(1, 28)
    assert Fraction(whole_legal, legal) <= 2 * Fraction(whole, total)
    assert Fraction(proper_legal, legal) <= 2 * Fraction(proper, total)
    return {"sample_space": total, "legal": legal,
            "legal_fraction": str(Fraction(legal, total)),
            "whole_block_hit_probability": str(Fraction(whole, total)),
            "proper_subset_hit_probability": str(Fraction(proper, total))}


def packing_check(k, n, partition, native, passes, seed):
    rng = random.Random(seed)
    m = n // 2
    replicas = m ** (len(partition) - 1)
    native_degree = max(Counter(x for t in native for x in t).values())
    free = tuple(i for i in range(k) if all(i not in h[0] for h in partition))
    occupied = set()
    loads = Counter()
    freshness = defaultdict(set)
    rejected = 0
    stage_count = 0
    pass_caps = []
    for number in range(passes):
        pass_loads = Counter()
        for j, inner in enumerate(native):
            for replica in range(replicas):
                forbidden = freshness[j, replica] | {abs(t) for x in inner for t in x}
                count = sum(pure(len(h[0]))[1] for h in partition)
                choices = [a for a in range(1, m + 1) if a not in forbidden]
                assert len(choices) >= count
                for attempt in range(10000):
                    selected = rng.sample(choices, count)
                    cursor = 0
                    factors = []
                    for axes, signs in partition:
                        size = pure(len(axes))[1]
                        factors.append((axes, reflected_selector(axes, signs, selected[cursor:cursor + size])))
                        cursor += size
                    factors.append((free, inner))
                    stage = put_product(k, factors)
                    if occupied & stage.keys():
                        rejected += 1
                        continue
                    assert contraction(stage, k, partition) == inner
                    for x in stage:
                        assert all(-m <= a <= m for a in x)
                        for key in point_line_keys(x):
                            pass_loads[key] += 1
                            loads[key] += 1
                    occupied.update(stage)
                    freshness[j, replica].update(selected)
                    stage_count += 1
                    break
                else:
                    raise AssertionError("finite independent packing exhausted")
        pass_caps.append(max(pass_loads.values()))
    # Check full-line enumeration a second way on the finite packed support.
    direct = Counter()
    for x in occupied:
        for axes, signs in signed_blocks(k):
            if len({s * x[i] for i, s in zip(axes, signs)}) == 1:
                direct[axes, signs, tuple(x[i] for i in range(k) if i not in axes)] += 1
    assert loads == direct
    return {"k": k, "n": n, "replicas_per_template": replicas,
            "native_templates": len(native), "native_point_degree": native_degree,
            "passes": passes, "stages": stage_count, "cells": len(occupied),
            "max_full_line_load": max(loads.values()), "pass_caps": pass_caps,
            "rejections": rejected}


def ledger(k):
    a = 2 * k - 3
    b = k // 2
    d = a + b
    delta = Fraction(3, 20 * (d + 1))
    eta = delta / 4
    top = Fraction(3, 5) + d * delta
    assert top == Fraction(3, 4) - Fraction(3, 20 * (d + 1))
    margins = {
        "capacity": delta - eta,
        "deletion_and_midpoint": Fraction(4, 5) - top,
        "baseline_completion": Fraction(1, 10),
        "bundle_fluctuation": Fraction(3, 5) - top / 2,
        "line_occupancy": 1 - top,
        "prime_target_vs_X": k - Fraction(3, 5) * (k + 1),
    }
    assert margins["deletion_and_midpoint"] == Fraction(1, 20) + Fraction(3, 20 * (d + 1))
    assert margins["bundle_fluctuation"] == Fraction(9, 40) + Fraction(3, 40 * (d + 1))
    assert all(x > 0 for x in margins.values())
    for blocks in range(1, b + 1):
        complement = k - 2 * blocks
        assert complement + blocks - 1 <= k - blocks - 1 <= k - 2
        assert k + Fraction(3, 5) - complement > 0
    return {"k": k, "axis_levels": a, "partition_levels": b, "D": d,
            "eta": str(eta), "top_exponent": str(top),
            "margins": {x: str(v) for x, v in margins.items()}}


def must_reject(call):
    try:
        call()
    except (AssertionError, ValueError):
        return
    raise AssertionError("negative control unexpectedly passed")


def require(value):
    assert value


def negative_controls():
    count = 0
    p = (((0, 1), (1, 1)),)
    good, factors, _ = native_stage(4, p)
    bad = dict(good)
    first = next(iter(bad))
    bad[first] *= -1
    must_reject(lambda: check_signature(4, p, bad, factors)); count += 1

    # A complementary tensor with zero axes but nonzero diagonal is insufficient.
    weak = put_product(2, [((0,), {(1,): 1, (2,): -1}),
                           ((1,), {(1,): 1, (3,): -1})])
    bad, factors, _ = native_stage(4, p, weak)
    must_reject(lambda: check_signature(4, p, bad, factors)); count += 1

    # Sharing an orbit between the outer selector and a genuine K_1 leaks a body.
    q = reflected_selector((0, 1), (1, 1), (1, 2, 3))
    factors = [((0, 1), q), ((2,), {(1,): 1, (4,): -1})]
    bad = put_product(3, factors)
    must_reject(lambda: check_signature(3, p, bad, factors)); count += 1

    # Omitting a required pair family preserves axes but leaves a nonzero target.
    omitted, _, _ = native_stage(5, p)
    must_reject(lambda: require(is_kernel(omitted, 5))); count += 1

    # Entrywise nearest-integer rounding need not retain a kernel.
    rounded = {x: nearest(Fraction(a, 2)) for x, a in generic_kernel(2).items()}
    must_reject(lambda: require(is_kernel(sparse(rounded), 2))); count += 1

    # Trace amplification cannot be assigned an unscaled original-line budget.
    must_reject(lambda: require(Fraction(9 ** 2, 1) <= 3 ** 2)); count += 1

    # Small total volume does not imply a small line or section load.
    full_line = {(t, 0, 0, 0) for t in range(-8, 9)}
    assert len(full_line) * 100 < 17 ** 4
    loads = Counter(key for x in full_line for key in point_line_keys(x))
    must_reject(lambda: require(max(loads.values()) < 17)); count += 1

    # Without reservoir orbit freshness, many stages can meet the same line,
    # and complementary central scalar states can have unbounded line range.
    stages = []
    for i in range(64):
        outer = reflected_selector((0, 1), (1, 1), (20 + 3*i, 21 + 3*i, 22 + 3*i))
        inner_labels = (7, 5, 6) if i < 32 else (5, 7, 6)
        inner = reflected_selector((2, 3), (1, 1), inner_labels)
        stages.append(put_product(4, [((0, 1), outer), ((2, 3), inner)]))
    assert sum(len(t) for t in stages) == len(set(x for t in stages for x in t))
    line_coefficients = [contraction(t, 4, (((0, 1), (1, 1)),)).get((5, 6), 0) for t in stages]
    assert line_coefficients == [1] * 32 + [-1] * 32
    # Select the first half or the second half: scalar sums equal, line sums differ by 64 gaps.
    must_reject(lambda: require(abs(sum(line_coefficients[:32]) - sum(line_coefficients[32:])) <= 16)); count += 1

    before, after = actual_trade(good, 6)
    duplicate = dict(before)
    keys = list(duplicate)
    duplicate[keys[0]] = duplicate[keys[1]]
    must_reject(lambda: validate_trade(good, duplicate, after, 6)); count += 1
    composite = dict(before)
    composite[keys[0]] = 21
    must_reject(lambda: validate_trade(good, composite, after, 6)); count += 1
    must_reject(lambda: require((8 * 1) % 8 == 2)); count += 1
    must_reject(lambda: pow(2, -1, 8)); count += 1
    must_reject(lambda: require(Fraction(3, 5) + 100 * Fraction(1, 100) < Fraction(4, 5))); count += 1
    # A list of line targets has no cell-indexed bijective first-prime certificate.
    must_reject(lambda: require(set({"target": 101}) == set(good))); count += 1
    return count


def run(root, previous_root=None):
    bindings = check_bindings(root)
    if previous_root is not None:
        bindings += check_bindings(previous_root, PREVIOUS_BINDINGS)
    geometry = [geometry_check(k, n) for k, n in [(2, 3), (3, 3), (4, 3), (5, 3), (6, 3), (4, 5)]]
    selector_sizes = {}
    for r in range(2, 5):
        q, alphabet = pure(r)
        assert set(q.values()) == {-1, 1}
        for h in signed_blocks(r):
            got = contraction(q, r, (h,))
            assert got == ({(): 1} if len(h[0]) == r and all(s == 1 for s in h[1]) else {})
        selector_sizes[r] = [alphabet, len(q)]
    fixtures = [
        (2, (((0, 1), (1, -1)),)),
        (3, (((0, 1), (1, 1)),)),
        (4, (((0, 1), (1, -1)), ((2, 3), (1, 1)))),
        (4, (((0, 1, 2), (1, -1, 1)),)),
        (5, (((0, 1), (1, 1)),)),
        (5, (((0, 1), (1, -1)), ((2, 3), (1, -1)))),
        (6, (((0, 1), (1, 1)), ((2, 3), (1, -1)), ((4, 5), (1, 1)))),
        (6, (((0, 1, 2), (1, -1, -1)), ((3, 4, 5), (1, 1, -1)))),
        (6, (((0, 1), (1, -1)),)),
    ]
    signature_equations = 0
    trades = 0
    for k, p in fixtures:
        stage, factors, inner = native_stage(k, p)
        check_signature(k, p, stage, factors)
        signature_equations += len(signed_blocks(k)) + len(signed_partitions(k))
        if k in (4, 5) and len(p) == 2:
            before, after = actual_trade(stage, 6)
            assert contraction(sum_tensors((1, after), (-1, before)), k, p) == {x: 6*a for x, a in inner.items()}
            trades += 1
    splits = [split_check(d, q) for d in range(1, 5) for q in (1, 2, 7, 25, 37)]
    hierarchy = [{"k": k, "modulus": modulus, "nonzero_steps": hierarchy_check(k, modulus)}
                 for k, modulus in [(4, None), (5, None), (6, None), (4, 4), (4, 6), (5, 8), (5, 9), (6, 12)]]
    residue_checks = 0
    for h in (1, 2, 3, 4, 6, 8, 9, 12, 15):
        g = 2*h
        for half_error in range(-2*h, 2*h + 1):
            a = half_error % h
            actual_gap = g + 2
            assert (2*half_error - a*actual_gap) % g == 0
            residue_checks += 1
    probability = exact_packing_probabilities()
    partition2 = (((0, 1), (1, -1)), ((2, 3), (1, 1)))
    partition3 = partition2 + (((4, 5), (1, -1)),)
    packed = [
        packing_check(4, 49, partition2, [{(): 1}], 3, 2026110301),
        packing_check(5, 49, partition2, [{(0,): 1, (1,): -1}, {(1,): 1, (-1,): -1}], 3, 2026110302),
        packing_check(6, 43, partition3, [{(): 1}], 2, 2026110303),
    ]
    resource_rows = [ledger(k) for k in range(2, 257)]
    return {"revision": REVISION, "tree": TREE, "source_bindings": bindings,
            "geometry": geometry, "independent_selector_sizes": selector_sizes,
            "native_signature_fixtures": len(fixtures), "signature_equations": signature_equations,
            "actual_partial_prime_trades": trades, "compatible_splits": len(splits),
            "complete_bundle_controls": complete_bundle_checks(),
            "hierarchy_checks": hierarchy, "composite_residue_checks": residue_checks,
            "exact_packing_probabilities": probability, "random_packing_fixtures": packed,
            "rational_resource_dimensions": len(resource_rows), "k5": ledger(5), "k6": ledger(6),
            "negative_controls": negative_controls(),
            "imports_author_code": False, "full_prime_array_certificate": False,
            "asymptotic_or_formal_proof_by_computation": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--previous-source-root", type=Path)
    args = parser.parse_args()
    print(json.dumps(run(args.source_root, args.previous_source_root), indent=2, sort_keys=True))
