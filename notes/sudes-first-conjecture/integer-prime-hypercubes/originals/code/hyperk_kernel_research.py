#!/usr/bin/env python3
"""Exact controls for pure selectors and the open distributed-kernel route.

No produced tensor is labeled a prime-array arrangement.  All arithmetic is
integer; the checker enumerates signed line keys independently of the
selector recursion.  Python 3.11+; standard library only.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from functools import lru_cache
from itertools import combinations, product
from math import comb

Tensor = dict[tuple[int, ...], int]
Block = tuple[tuple[int, ...], tuple[int, ...]]


def clean(a: Tensor) -> Tensor:
    return {x: v for x, v in a.items() if v}


def add(a: Tensor, b: Tensor, scalar: int = 1) -> Tensor:
    out = defaultdict(int, a)
    for x, v in b.items():
        out[x] += scalar * v
    return clean(dict(out))


def product_tensor(factors: list[tuple[tuple[int, ...], Tensor]], d: int) -> Tensor:
    """Tensor factors with disjoint coordinate sets, preserving coordinate order."""
    assert sorted(i for coords, _ in factors for i in coords) == list(range(d))
    work: dict[tuple[int | None, ...], int] = {(None,) * d: 1}
    for coords, factor in factors:
        nxt = {}
        for old, a in work.items():
            for values, b in factor.items():
                x = list(old)
                for i, value in zip(coords, values):
                    assert x[i] is None
                    x[i] = value
                key = tuple(x)
                assert key not in nxt
                nxt[key] = a * b
        work = nxt
    return {tuple(int(v) for v in x): c for x, c in work.items()}


def blocks_on(coords: tuple[int, ...], signed: bool = True):
    for size in range(2, len(coords) + 1):
        for c in combinations(coords, size):
            tails = product((-1, 1), repeat=size - 1) if signed else [((1,) * (size - 1))]
            for tail in tails:
                yield c, (1,) + tuple(tail)


def block_collections(d: int, *, signed: bool, proper_only: bool = False):
    """Each set of disjoint blocks appears once; unused coordinates are allowed."""
    def rec(coords):
        if not coords:
            yield ()
            return
        first = coords[0]
        for rest in rec(coords[1:]):
            yield rest
        for c, signs in blocks_on(coords, signed=signed):
            if first not in c or (proper_only and len(c) == d):
                continue
            remaining = tuple(i for i in coords if i not in c)
            for rest in rec(remaining):
                yield ((c, signs),) + rest
    yield from rec(tuple(range(d)))


def full_signed_signature(a: Tensor, d: int) -> dict[tuple, int]:
    """Independent geometric image of every full signed-coordinate line.

    For a support cell, the first varying coordinate determines the line
    parameter.  All other varying coordinates are tested literally.  Each
    full-line key is emitted once, even for the center.
    """
    out = defaultdict(int)
    for size in range(1, d + 1):
        for c in combinations(range(d), size):
            fixed = tuple(i for i in range(d) if i not in c)
            for tail in product((-1, 1), repeat=size - 1):
                signs = (1,) + tail
                for x, value in a.items():
                    t = x[c[0]]
                    if all(x[i] == sign * t for i, sign in zip(c, signs)):
                        key = (c, signs, tuple(x[i] for i in fixed))
                        out[key] += value
    return clean(dict(out))


def contraction(a: Tensor, d: int, block: Block) -> Tensor:
    c, signs = block
    fixed = tuple(i for i in range(d) if i not in c)
    out = defaultdict(int)
    for x, value in a.items():
        t = x[c[0]]
        if all(x[i] == sign * t for i, sign in zip(c, signs)):
            out[tuple(x[i] for i in fixed)] += value
    return clean(dict(out))


def coordinate_pairs(a: Tensor, d: int, axis: int):
    assert set(a.values()) <= {-1, 1}
    fibers = defaultdict(lambda: ([], []))
    for x, sign in a.items():
        key = tuple(x[i] for i in range(d) if i != axis)
        fibers[key][0 if sign > 0 else 1].append(x)
    out = []
    for pos, neg in fibers.values():
        assert len(pos) == len(neg), "nonzero axis marginal"
        out.extend(zip(sorted(pos), sorted(neg)))
    assert len(out) * 2 == len(a)
    assert len({x for pair in out for x in pair}) == len(a)
    return out


@lru_cache(None)
def pure_selector(b: int) -> tuple[Tensor, int]:
    """The disjoint-alphabet inclusion-exclusion construction PS(b)."""
    assert b >= 2
    original = [{(1,): 1, (i + 2,): -1} for i in range(b)]
    next_label = b + 2
    selectors = {}
    for c, signs in blocks_on(tuple(range(b)), signed=False):
        if len(c) == b:
            continue
        sub, alphabet = pure_selector(len(c))
        shift = next_label - 1
        selectors[c] = {tuple(v + shift for v in x): z for x, z in sub.items()}
        next_label += alphabet
    out = {}
    for pi in block_collections(b, signed=False, proper_only=True):
        covered = {i for c, _ in pi for i in c}
        factors = [(c, selectors[c]) for c, _ in pi]
        factors += [((i,), original[i]) for i in range(b) if i not in covered]
        term = product_tensor(factors, b)
        assert not out.keys() & term.keys(), "pure-selector terms overlap"
        sign = (-1) ** len(pi)
        out.update({x: sign * value for x, value in term.items()})
    return out, next_label - 1


def selector_invoices(max_b: int):
    alphabets = {0: 0, 1: 0}
    supports = {0: 1, 1: 0}
    for b in range(2, max_b + 1):
        alphabets[b] = b + 1 + sum(comb(b, c) * alphabets[c] for c in range(2, b))
        f = [1]
        for j in range(1, b + 1):
            value = 2 * f[j - 1]
            value += sum(comb(j - 1, c - 1) * supports[c] * f[j - c]
                         for c in range(2, min(j, b - 1) + 1))
            f.append(value)
        supports[b] = f[b]
    return alphabets, supports


def raw_product(pairs: tuple[tuple[int, int], ...]) -> Tensor:
    assert all(u != v for u, v in pairs)
    return product_tensor([((i,), {(u,): 1, (v,): -1})
                           for i, (u, v) in enumerate(pairs)], len(pairs))


def local_projector(pairs: tuple[tuple[int, int], ...]) -> Tensor:
    """LP(d), retaining one shared signed witness sum per signed block."""
    d = len(pairs)
    point = [{u: 1, v: -1} for u, v in pairs]
    next_label = max(abs(t) for pair in pairs for t in pair) + 1
    selector_sums = {}
    for block in blocks_on(tuple(range(d)), signed=True):
        c, signs = block
        witnesses = []
        for t in pairs[c[0]]:
            value = 1
            for i, sigma in zip(c, signs):
                value *= point[i].get(sigma * t, 0)
            if value:
                witnesses.append((t, value))
        if not witnesses:
            continue
        sub, alphabet = pure_selector(len(c))
        combined = {}
        for t, sign in witnesses:
            shift = next_label - 1
            term = {tuple(sigma * (v + shift) for sigma, v in zip(signs, x)): sign * z
                    for x, z in sub.items()}
            assert not combined.keys() & term.keys()
            combined.update(term)
            next_label += alphabet
        selector_sums[block] = combined
    out = {}
    for pi in block_collections(d, signed=True):
        if any(block not in selector_sums for block in pi):
            continue
        covered = {i for c, _ in pi for i in c}
        factors = [(c, selector_sums[(c, signs)]) for c, signs in pi]
        factors += [((i,), {(pairs[i][0],): 1, (pairs[i][1],): -1})
                    for i in range(d) if i not in covered]
        term = product_tensor(factors, d)
        assert not out.keys() & term.keys(), "decorated projector terms overlap"
        sign = (-1) ** len(pi)
        out.update({x: sign * value for x, value in term.items()})
    return out


def colored_restriction(a: Tensor, allowed: set[int]) -> Tensor:
    return {x: value for x, value in a.items() if all(abs(v) in allowed for v in x)}


def run_self_test():
    counts = defaultdict(int)
    alphabets, supports = selector_invoices(7)
    expected = {2: (3, 4), 3: (13, 32), 4: (75, 416), 5: (541, 7552),
                6: (4683, 176128), 7: (47293, 5018624)}
    assert {b: (alphabets[b], supports[b]) for b in expected} == expected
    counts["symbolic_invoices"] = len(expected)
    partition_counts = [1]
    for d in range(1, 7):
        p_d = partition_counts[d - 1] + sum(
            comb(d - 1, s - 1) * 2 ** (s - 1) * partition_counts[d - s]
            for s in range(2, d + 1))
        partition_counts.append(p_d)
        assert p_d == sum(1 for _ in block_collections(d, signed=True))
        if d >= 2:
            witness_cap = 2 * ((3 ** d - 1) // 2 - d)
            palette_cap = 2 * d + witness_cap * alphabets[d] + 1
            assert palette_cap > 2 * d + (witness_cap - 1) * alphabets[d]
            counts["palette_constant_diagnostics"] += 1
    for b in range(2, 6):
        q, alphabet = pure_selector(b)
        assert alphabet == alphabets[b]
        assert len(q) == supports[b]
        assert set(q.values()) == {-1, 1}
        assert full_signed_signature(q, b) == {(tuple(range(b)), (1,) * b, ()): 1}
        for axis in range(b):
            pairs = coordinate_pairs(q, b, axis)
            delta = defaultdict(int)
            for pos, neg in pairs:
                delta[pos] += 30
                delta[neg] -= 30
            assert dict(delta) == {x: 30 * value for x, value in q.items()}
            counts["pure_selector_coordinate_pairings"] += 1
        reflected = {tuple((-1 if i % 2 else 1) * v for i, v in enumerate(x)): z
                     for x, z in q.items()}
        assert full_signed_signature(reflected, b) == {
            (tuple(range(b)), tuple(-1 if i % 2 else 1 for i in range(b)), ()): 1}
        counts["pure_selector_full_signatures"] += 2

    cases = [((1, 2), (1, 2)), ((1, -1), (1, -1)), ((0, 1), (0, -1)),
             ((1, 2), (3, 4)), ((1, 2), (1, 3), (1, 4)),
             ((1, -1), (1, -1), (1, -1)), ((0, 1), (0, -1), (2, 3)),
             ((1, 2), (1, 2), (3, 4), (3, 4)),
             ((1, -1), (1, -1), (1, -1), (1, -1)),
             ((0, 1), (0, 2), (0, 3), (4, -4)),
             ((1, 2), (1, 3), (4, 5), (4, 6), (7, 8))]
    for raw in cases:
        q = local_projector(raw)
        assert set(q.values()) <= {-1, 1}
        assert not full_signed_signature(q, len(raw))
        for axis in range(len(raw)):
            coordinate_pairs(q, len(raw), axis)
            counts["local_kernel_coordinate_pairings"] += 1
        counts["local_kernel_full_signatures"] += 1

    q = raw_product(((1, 2), (1, 3)))
    qp = raw_product(((5, 6), (5, 7)))
    f = {(1,): 1, (4,): -1}
    bad = product_tensor([((0, 1), add(q, qp, -1)), ((2,), f)], 3)
    assert not full_signed_signature(add(q, qp, -1), 2)
    assert not full_signed_signature(f, 1)
    image = full_signed_signature(bad, 3)
    assert image[((0, 1, 2), (1, 1, 1), ())] == 1
    assert contraction(bad, 3, ((0, 2), (1, 1))) == {(1,): 1, (3,): -1}
    counts["forbidden_endpoint_counterexamples"] += 1
    safe_f = {(8,): 1, (9,): -1}
    safe = product_tensor([((0, 1), add(q, qp, -1)), ((2,), safe_f)], 3)
    assert not full_signed_signature(safe, 3)
    counts["endpoint_disjoint_repair_controls"] += 1

    kernel = add(q, qp, -1)
    independently_projected = add(local_projector(((1, 2), (1, 3))),
                                 local_projector(((5, 6), (5, 7))), -1)
    assert not full_signed_signature(independently_projected, 2)
    assert independently_projected != kernel
    assert not full_signed_signature(add(kernel, independently_projected, -1), 2)
    counts["independent_marker_reconstruction_counterexamples"] += 1
    red = colored_restriction(kernel, {1, 2, 3})
    blue = colored_restriction(kernel, {5, 6, 7})
    assert add(red, blue) == kernel
    assert full_signed_signature(red, 2)[((0, 1), (1, 1), ())] == 1
    assert full_signed_signature(blue, 2)[((0, 1), (1, 1), ())] == -1
    counts["color_restriction_counterexamples"] += 1

    # Independent negative controls: correct labels cannot conceal bad geometry.
    q3, _ = pure_selector(3)
    corruptions = []
    x = next(iter(q3))
    changed = dict(q3); changed[x] *= -1; corruptions.append(changed)
    missing = dict(q3); missing.pop(x); corruptions.append(missing)
    doubled = dict(q3); doubled[x] *= 2; corruptions.append(doubled)
    for a in corruptions:
        try:
            assert set(a.values()) <= {-1, 1}
            assert full_signed_signature(a, 3) == {((0, 1, 2), (1, 1, 1), ()): 1}
        except AssertionError:
            counts["corrupted_selectors_rejected"] += 1
        else:
            raise AssertionError("corrupted selector passed")
    print("PASS", dict(sorted(counts.items())))
    print("Boundary: local templates and exact obstruction controls; no full prime arrangement or BK(d) proof.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    run_self_test()
