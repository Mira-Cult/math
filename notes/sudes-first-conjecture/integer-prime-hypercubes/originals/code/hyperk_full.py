#!/usr/bin/env python3
"""Exact finite controls for the all-dimension partition composition.

These controls test signatures, legal local prime trades, shared-trace
splitting, and symbolic resource identities. They do not certify a full
higher-dimensional prime array or an eventual threshold.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import comb
import random

from hyperk_kernel_research import pure_selector


def signed_blocks(k):
    for size in range(1, k + 1):
        for block in combinations(range(k), size):
            for signs in product((-1, 1), repeat=size - 1):
                yield block, (1,) + signs


def partitions(k):
    """Every disjoint collection of normalized nonaxis signed blocks once."""
    def visit(remaining):
        if not remaining:
            yield ()
            return
        first, rest = remaining[0], remaining[1:]
        yield from visit(rest)
        for r in range(1, len(rest) + 1):
            for tail in combinations(rest, r):
                block = (first,) + tail
                left = tuple(x for x in rest if x not in tail)
                for signs in product((-1, 1), repeat=r):
                    for after in visit(left):
                        yield ((block, (1,) + signs),) + after
    yield from visit(tuple(range(k)))


def clean(tensor):
    return {cell: value for cell, value in tensor.items() if value}


def add(target, source, scalar=1):
    answer = defaultdict(int, target)
    for cell, value in source.items():
        answer[cell] += scalar * value
    return clean(answer)


def tensor_product(k, factors):
    answer = {tuple([None] * k): 1}
    for coords, tensor in factors:
        new = defaultdict(int)
        for old, coefficient in answer.items():
            for point, value in tensor.items():
                cell = list(old)
                for i, x in zip(coords, point):
                    assert cell[i] is None
                    cell[i] = x
                new[tuple(cell)] += coefficient * value
        answer = clean(new)
    assert all(None not in cell for cell in answer)
    return answer


def contract(tensor, k, partition):
    """Independent simultaneous contraction, using original coordinates."""
    used = {i for block, _ in partition for i in block}
    outside = tuple(i for i in range(k) if i not in used)
    answer = defaultdict(int)
    for cell, value in tensor.items():
        if all(all(cell[i] == sign * cell[block[0]]
                   for i, sign in zip(block, signs))
               for block, signs in partition):
            answer[tuple(cell[i] for i in outside)] += value
    return clean(answer)


def selector(block, signs, start):
    native, label_count = pure_selector(len(block))
    transformed = {
        tuple(sign * (start + value) for sign, value in zip(signs, cell)): coefficient
        for cell, coefficient in native.items()
    }
    return transformed, start + label_count + 7


def generic_kernel(d, start=10000):
    if not d:
        return {(): 1}
    factors = [((i,), {(start + 3 * i,): 1, (start + 3 * i + 1,): -1})
               for i in range(d)]
    return tensor_product(d, factors)


def native_trade(k, partition, inner=None):
    used = {i for block, _ in partition for i in block}
    outside = tuple(i for i in range(k) if i not in used)
    if inner is None:
        inner = generic_kernel(len(outside))
    factors = []
    cursor = 50
    for block, signs in partition:
        q, cursor = selector(block, signs, cursor)
        factors.append((block, q))
    factors.append((outside, inner))
    return tensor_product(k, factors), factors, inner


def verify_signature(k, partition, tensor, factors):
    native = set(partition)
    for block in signed_blocks(k):
        got = contract(tensor, k, (block,))
        if block not in native:
            assert not got, ("unexpected full line", k, partition, block, got)
    for rho in partitions(k):
        got = contract(tensor, k, rho)
        if not set(rho) <= native:
            assert not got, ("unexpected partition", k, partition, rho)
            continue
        removed = {i for block, _ in rho for i in block}
        outside = tuple(i for i in range(k) if i not in removed)
        relabel = {old: new for new, old in enumerate(outside)}
        kept = [(tuple(relabel[i] for i in coords), values)
                for coords, values in factors if not set(coords) <= removed]
        # An empty inner scalar is retained even when no free coordinates remain.
        if not outside:
            expected = {(): 1}
        else:
            expected = tensor_product(len(outside), kept)
        assert got == expected, ("wrong native signature", k, partition, rho)


def prime(q):
    if q < 2:
        return False
    if q % 2 == 0:
        return q == 2
    factor = 3
    while factor * factor <= q:
        if q % factor == 0:
            return False
        factor += 2
    return True


def physical_trade(tensor, gap=6):
    positive = sorted(x for x, c in tensor.items() if c == 1)
    negative = sorted(x for x, c in tensor.items() if c == -1)
    assert len(positive) == len(negative)
    used = set()
    before, after = {}, {}
    low = 101
    for plus, minus in zip(positive, negative):
        while not (prime(low) and prime(low + gap)
                   and low not in used and low + gap not in used):
            low += 2
        used.update((low, low + gap))
        before[plus], before[minus] = low, low + gap
        after[plus], after[minus] = low + gap, low
        low += 2
    assert sorted(before.values()) == sorted(after.values())
    assert len(set(before.values())) == len(before)
    assert all(prime(value) for value in before.values())
    delta = {x: after[x] - before[x] for x in before}
    assert delta == {x: gap * value for x, value in tensor.items()}
    return before, after


def round_fraction(x):
    return (2 * x.numerator + x.denominator) // (2 * x.denominator)


def compatible_split(templates, coefficients, q):
    total = {}
    for n, coefficient in zip(templates, coefficients):
        total = add(total, n, coefficient)
    previous = {}
    pieces = []
    for j in range(1, q + 1):
        current = {}
        for n, coefficient in zip(templates, coefficients):
            current = add(current, n, round_fraction(Fraction(j * coefficient, q)))
        pieces.append(add(current, previous, -1))
        previous = current
    assert previous == total
    reconstructed = {}
    for piece in pieces:
        reconstructed = add(reconstructed, piece)
    assert reconstructed == total
    return total, pieces


def point_lines(point):
    """Complete canonical full-line keys containing one point."""
    k = len(point)
    for block, signs in signed_blocks(k):
        t = point[block[0]]
        if all(point[i] == sign * t for i, sign in zip(block, signs)):
            yield block, signs, tuple(point[i] for i in range(k) if i not in block)


def packing_fixture(k, n, seed):
    """Finite rejection-sampling replay; not an asymptotic packing proof."""
    rng = random.Random(seed)
    m = n // 2
    partition = (((0, 1), (1, -1)), ((2, 3), (1, 1)))
    free = tuple(range(4, k))
    inner = {(): 1} if not free else {(0,): 1, (1,): -1}
    occupied = set()
    loads = Counter()
    rejected = 0
    for _replica in range(m):
        used_labels = set()
        for _stage in range(2):
            for _attempt in range(10000):
                choices = [a for a in range(1, m + 1)
                           if a not in used_labels and a != 1]
                labels = rng.sample(choices, 6)
                factors = []
                for j, (block, signs) in enumerate(partition):
                    a, b, c = labels[3 * j:3 * j + 3]
                    q = {(signs[0] * a, signs[1] * a): 1,
                         (signs[0] * a, signs[1] * c): -1,
                         (signs[0] * b, signs[1] * a): -1,
                         (signs[0] * b, signs[1] * c): 1}
                    factors.append((block, q))
                factors.append((free, inner))
                support = tensor_product(k, factors)
                if occupied.intersection(support):
                    rejected += 1
                    continue
                occupied.update(support)
                used_labels.update(labels)
                for cell in support:
                    loads.update(point_lines(cell))
                break
            else:
                raise AssertionError("finite packing exhausted candidates")
    assert len(occupied) == m * 2 * (16 if k == 4 else 32)
    return {"k": k, "n": n, "stages": 2 * m, "cells": len(occupied),
            "max_full_line_load": max(loads.values()), "rejections": rejected}


def resources(k):
    axis = 2 * k - 3
    depth = axis + k // 2
    gap = Fraction(3, 20 * (depth + 1))
    eta = gap / 4
    endpoint = Fraction(3, 5) + depth * gap
    margins = {
        "capacity": gap - eta,
        "deletion_midpoint": Fraction(4, 5) - endpoint,
        "baseline": Fraction(3, 5) - Fraction(1, 2),
        "bundle_fluctuation": Fraction(3, 5) - endpoint / 2,
        "occupancy": 1 - endpoint,
    }
    assert all(value > 0 for value in margins.values())
    assert margins["deletion_midpoint"] > Fraction(1, 20)
    assert margins["bundle_fluctuation"] > Fraction(9, 40)
    for b in range(1, k // 2 + 1):
        for d in range(k - 2 * b + 1):
            assert d + b - 1 <= k - b - 1 <= k - 2
            assert k + Fraction(3, 5) - d > 0
    return {"k": k, "axis_levels": axis, "partition_levels": k // 2,
            "depth": depth, "eta": str(eta), "endpoint": str(endpoint),
            "margins": {name: str(value) for name, value in margins.items()}}


def partition_counts(maximum):
    counts = [1]
    for k in range(1, maximum + 1):
        counts.append(counts[k - 1] + sum(
            comb(k - 1, r - 1) * 2 ** (r - 1) * counts[k - r]
            for r in range(2, k + 1)))
    return counts


def must_fail(callback):
    try:
        callback()
    except (AssertionError, ValueError):
        return
    raise AssertionError("negative control was accepted")


def run_checks():
    signatures = 0
    trades = 0
    fixtures = [
        (2, (((0, 1), (1, 1)),)),
        (3, (((0, 1), (1, -1)),)),
        (3, (((0, 1, 2), (1, -1, 1)),)),
        (4, (((0, 1), (1, 1)), ((2, 3), (1, -1)))),
        (4, (((0, 1, 2), (1, -1, -1)),)),
        (5, (((0, 1), (1, -1)), ((2, 3), (1, 1)))),
        (5, (((0, 1), (1, -1)),)),
        (6, (((0, 1), (1, 1)), ((2, 3), (1, -1)), ((4, 5), (1, -1)))),
        (6, (((0, 1, 2), (1, -1, 1)), ((3, 4), (1, -1)))),
        (6, (((0, 1), (1, -1)),)),
    ]
    for k, partition in fixtures:
        tensor, factors, _inner = native_trade(k, partition)
        assert set(tensor.values()) <= {-1, 1}
        verify_signature(k, partition, tensor, factors)
        signatures += 1
        if k in (4, 5) and len(partition) == 2:
            before, after = physical_trade(tensor)
            assert contract(add(after, before, -1), k, partition) == {
                cell: 6 * value for cell, value in _inner.items()}
            trades += 1

    splits = 0
    for d in range(1, 5):
        templates = [generic_kernel(d, 100 + 20 * j) for j in range(3)]
        for q in (1, 2, 7, 25):
            total, pieces = compatible_split(templates, (127, -98, 53), q)
            degree = max(Counter(x for t in templates for x in t).values())
            for piece in pieces:
                assert all(not contract(piece, d, (h,)) for h in signed_blocks(d))
                bound = Fraction(max(map(abs, total.values())), q) + degree
                assert max(map(abs, piece.values()), default=0) <= bound
            splits += 1

    # Native-pair images alone do not check the other signed line families.
    bad_inner = tensor_product(2, [((0,), {(3,): 1, (4,): -1}),
                                  ((1,), {(3,): 1, (5,): -1})])
    bad, factors, _ = native_trade(4, (((0, 1), (1, 1)),), bad_inner)
    must_fail(lambda: verify_signature(4, (((0, 1), (1, 1)),), bad, factors))
    good, factors, _ = native_trade(4, fixtures[3][1])
    broken = dict(good)
    key = next(iter(broken))
    broken[key] *= -1
    must_fail(lambda: verify_signature(4, fixtures[3][1], broken, factors))
    # A shared trace of b=3 has n^2 amplification. Replicas pay this factor.
    _check_trace_budget(n=9, b=3, replicas=16)
    must_fail(lambda: _check_trace_budget(n=9, b=3, replicas=1))
    # A fixed positive exponent increment cannot be used for unbounded depth.
    must_fail(lambda: _require(Fraction(3, 5) + 100 * Fraction(1, 100)
                               < Fraction(4, 5)))
    ledger = [resources(k) for k in range(2, 129)]
    types = partition_counts(6)
    assert types == [sum(1 for _ in partitions(k)) for k in range(7)]
    packing = [packing_fixture(4, 61, 20261103), packing_fixture(5, 61, 20261104)]
    return {"partition_signatures": signatures, "legal_partial_prime_trades": trades,
            "compatible_integer_splits": splits, "negative_controls": 4,
            "symbolic_dimensions": len(ledger),
            "partition_type_counts_k0_through_k6": types,
            "k5": resources(5), "k6": resources(6), "packing_fixtures": packing,
            "full_higher_dimensional_arrays_claimed": False}


def _require(condition):
    assert condition


def _check_trace_budget(n, b, replicas):
    assert Fraction(n ** (b - 1), replicas) <= 3 ** (b - 1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.parse_args()
    print(run_checks())
