#!/usr/bin/env python3
"""Exact diagnostic controls for the AF full signed-kernel absorber.

Standard library only. These tensors are not prime-array arrangements.
The signed-line checker below is independent of the selector recursion.
"""
from __future__ import annotations

from collections import Counter, defaultdict, deque
from itertools import combinations, product
from math import comb
from random import Random

from hyperk_kernel_research import (add, clean, pure_selector, local_projector,
    raw_product, product_tensor, coordinate_pairs, selector_invoices,
    block_collections)


def signature(tensor, d):
    out = defaultdict(int)
    for r in range(1, d + 1):
        for block in combinations(range(d), r):
            fixed = tuple(i for i in range(d) if i not in block)
            for tail in product((-1, 1), repeat=r - 1):
                signs = (1,) + tail
                for cell, value in tensor.items():
                    parameter = cell[block[0]]
                    if all(cell[i] == s * parameter for i, s in zip(block, signs)):
                        out[(block, signs, tuple(cell[i] for i in fixed))] += value
    return clean(dict(out))


def axis_margins(tensor, d):
    out = defaultdict(int)
    for cell, value in tensor.items():
        for i in range(d):
            out[(i, cell[:i] + cell[i + 1:])] += value
    return clean(dict(out))


def norm1(tensor):
    return sum(abs(v) for v in tensor.values())


def invoices(d):
    alphabets, supports = selector_invoices(d)
    alphabets[1] = supports[1] = 1
    central_alphabets = {0: 0}
    central_supports = {0: 1}
    for z in range(1, d + 1):
        central_alphabets[z] = z + sum(comb(z, b) * 2 ** (b - 1) * alphabets[b]
                                     for b in range(2, z + 1))
        central_supports[z] = sum(2 ** (z - sum(len(c) for c, _ in pi)) *
            prod(supports[len(c)] for c, _ in pi)
            for pi in block_collections(z, signed=True))
    return alphabets, supports, central_alphabets, central_supports


def prod(values):
    out = 1
    for value in values:
        out *= value
    return out


def rooted(b, t, palette, signs=None):
    signs = signs or (1,) * b
    assert t and abs(t) not in palette
    assert len(set(palette)) == len(palette) and all(v > 0 for v in palette)
    if b == 1:
        return {(signs[0] * t,): 1}
    base, alphabet = pure_selector(b)
    assert len(palette) >= alphabet - 1
    return {tuple(s * (t if v == 1 else palette[v - 2])
                  for s, v in zip(signs, cell)): coefficient
            for cell, coefficient in base.items()}


def rooted_difference(b, u, v, palette, signs=None):
    assert u != v
    return add(rooted(b, u, palette, signs), rooted(b, v, palette, signs), -1)


def central(z, palette):
    if z == 0:
        return {(): 1}
    base = local_projector(tuple((0, i + 1) for i in range(z)))
    needed = max(abs(t) for cell in base for t in cell)
    assert len(palette) >= needed
    return {tuple(0 if t == 0 else (1 if t > 0 else -1) * palette[abs(t) - 1]
                  for t in cell): value for cell, value in base.items()}


def cell_type(cell):
    zero = tuple(i for i, value in enumerate(cell) if value == 0)
    groups = defaultdict(list)
    for i, value in enumerate(cell):
        if value:
            groups[abs(value)].append(i)
    blocks, parameters = [], []
    for coords in sorted(groups.values(), key=lambda c: c[0]):
        t = cell[coords[0]]
        blocks.append((tuple(coords), tuple(cell[i] // t for i in coords)))
        parameters.append(t)
    return (zero, tuple(blocks)), tuple(parameters)


def lift(d, zero, blocks, pairs, palette):
    a, _, ca, _ = invoices(d)
    used = 0
    factors = []
    if zero:
        size = ca[len(zero)]
        factors.append((zero, central(len(zero), palette[used:used + size])))
        used += size
    assert len(blocks) == len(pairs)
    roots = {abs(t) for pair in pairs for t in pair}
    assert roots.isdisjoint(palette)
    for (coords, signs), (u, v) in zip(blocks, pairs):
        size = a[len(coords)] - 1
        q = rooted_difference(len(coords), u, v, palette[used:used + size], signs)
        factors.append((coords, q))
        used += size
    if not factors:
        return {(): 1}
    assert used <= len(palette)
    return product_tensor(factors, d)


def generic(pairs):
    if any(u == v or not u or not v for u, v in pairs):
        return False
    seen = set()
    for pair in pairs:
        current = {abs(t) for t in pair}
        if current & seen:
            return False
        seen |= current
    return True


def generic_decomposition(tensor, p, m, rng):
    assert not axis_margins(tensor, p)
    assert all(all(cell) and len({abs(t) for t in cell}) == p for cell in tensor)
    remaining = dict(tensor)
    terms = []
    history = [norm1(remaining)]
    while remaining:
        before = norm1(remaining)
        for _ in range(10000):
            anchors = tuple(rng.sample(range(1, m + 1), p))
            candidate = dict(remaining)
            new_terms = []
            for cell, value in remaining.items():
                if {abs(t) for t in cell}.isdisjoint(anchors):
                    pairs = tuple(zip(cell, anchors))
                    assert generic(pairs)
                    candidate = add(candidate, raw_product(pairs), -value)
                    new_terms.append((value, pairs))
            if norm1(candidate) * 2 <= before:
                remaining = candidate
                terms.extend(new_terms)
                break
        else:
            raise AssertionError('deterministic seeded search did not find contraction')
        assert not axis_margins(remaining, p)
        assert all(all(x) and len({abs(t) for t in x}) == p for x in remaining)
        history.append(norm1(remaining))
    assert sum(abs(value) for value, _ in terms) <= 2 * norm1(tensor)
    rebuilt = {}
    for value, pairs in terms:
        rebuilt = add(rebuilt, raw_product(pairs), value)
    assert rebuilt == tensor
    return terms, history


def signed_graph(m, radius):
    graph = {t: set() for t in range(-m, m + 1) if t}
    for orbit in range(1, m + 1):
        graph[orbit].add(-orbit)
        graph[-orbit].add(orbit)
        for shift in range(1, radius + 1):
            other = 1 + (orbit - 1 + shift) % m
            if other == orbit:
                continue
            for sign in (-1, 1):
                graph[sign * orbit].add(sign * other)
                graph[sign * other].add(sign * orbit)
    return graph


def simple_path(graph, start, end, forbidden):
    assert abs(start) not in forbidden and abs(end) not in forbidden
    previous = {start: None}
    queue = deque([start])
    while queue:
        x = queue.popleft()
        if x == end:
            path = []
            while x is not None:
                path.append(x)
                x = previous[x]
            return tuple(reversed(path))
        for y in sorted(graph[x]):
            if abs(y) not in forbidden and y not in previous:
                previous[y] = x
                queue.append(y)
    raise AssertionError('deleted graph disconnected')


def graph_subdivision(pairs, graph, palette):
    terms = [(1, pairs)]
    for axis in range(len(pairs)):
        following = []
        for coefficient, current in terms:
            forbidden = set(palette)
            for i, pair in enumerate(current):
                if i != axis:
                    forbidden.update(abs(t) for t in pair)
            path = simple_path(graph, *current[axis], forbidden)
            for u, v in zip(path, path[1:]):
                edge = tuple(sorted((u, v)))
                sign = 1 if edge == (u, v) else -1
                nxt = current[:axis] + (edge,) + current[axis + 1:]
                assert generic(nxt)
                following.append((coefficient * sign, nxt))
        terms = following
    multiplicities = Counter(pair_tuple for _, pair_tuple in terms)
    assert max(multiplicities.values(), default=0) <= 1
    return terms


def run():
    counts = Counter()
    rng = Random(20261103)
    for b in range(1, 6):
        a, _ = (1, 1) if b == 1 else (pure_selector(b)[1], None)
        palette = tuple(range(10, 10 + a - 1))
        signs = tuple(1 if i % 2 == 0 else -1 for i in range(b))
        for u, v in [(1, 2), (-1, -2), (1, -1), (-2, 3)]:
            q = rooted(b, u, palette, signs)
            assert signature(q, b) == {(tuple(range(b)), signs, ()): 1}
            native = {cell: value for cell, value in q.items()
                      if all(cell[i] == signs[i] * cell[0] for i in range(b))}
            assert native == {tuple(s * u for s in signs): 1}
            delta = rooted_difference(b, u, v, palette, signs)
            assert set(delta.values()) <= {-1, 1}
            assert not signature(delta, b)
            assert all(any(abs(t) not in palette for t in cell) for cell in delta)
            for axis in range(b):
                coordinate_pairs(delta, b, axis)
            counts['rooted_difference_signatures'] += 1
    for z in range(1, 5):
        _, _, ca, cs = invoices(z)
        c = central(z, tuple(range(1, ca[z] + 1)))
        assert len(c) == cs[z]
        assert c[(0,) * z] == 1 and set(c.values()) <= {-1, 1}
        assert not signature(c, z)
        for axis in range(z):
            coordinate_pairs(c, z, axis)
        counts['central_projectors'] += 1
    cases = [
        (3, (0,), (((1, 2), (1, -1)),), ((1, -1),)),
        (4, (), (((0, 1), (1, 1)), ((2, 3), (1, -1))), ((1, 2), (-3, 4))),
        (5, (0,), (((1, 2), (1, -1)), ((3, 4), (1, 1))), ((1, -1), (2, 3))),
        (6, (0, 1), (((2, 3), (1, -1)), ((4,), (1,)), ((5,), (1,))),
            ((1, 2), (-3, 4), (5, -5))),
        (6, (), (((0, 1, 2), (1, -1, 1)), ((3, 4, 5), (1, 1, -1))),
            ((1, -1), (2, -3))),
    ]
    for d, zero, blocks, pairs in cases:
        a, _, ca, _ = invoices(d)
        needed = ca[len(zero)] + sum(a[len(c)] - 1 for c, _ in blocks)
        palette = tuple(range(20, 20 + needed))
        lifted = lift(d, zero, blocks, pairs, palette)
        assert not signature(lifted, d)
        assert set(lifted.values()) <= {-1, 1}
        for axis in range(d):
            coordinate_pairs(lifted, d, axis)
        desired = raw_product(pairs)
        leading = {}
        for cell, value in lifted.items():
            typ, parameters = cell_type(cell)
            rank = len(parameters)
            assert rank >= len(blocks)
            if rank == len(blocks):
                assert typ == (zero, blocks)
                leading[parameters] = value
        assert leading == desired
        counts['strict_signed_stratum_lifts'] += 1
    for p, m in [(2, 64), (3, 256)]:
        width = m - 4
        cycle = {}
        for i in range(1, width + 1):
            cycle[(i, 1 + i % width)] = 1
            cycle[(i, 1 + (i + 1) % width)] = -1
        if p == 2:
            f = cycle
        else:
            f = product_tensor([((0, 1), cycle),
                 ((2,), {(m,): 1, (-m,): -1})], p)
        terms, history = generic_decomposition(f, p, m, rng)
        assert len(history) > 1
        counts['integer_generic_contractions'] += 1
    d, zero = 4, ()
    blocks = (((0, 1), (1, 1)), ((2, 3), (1, -1)))
    palette = (1, 2, 3, 4)
    pairs = ((6, -56), (-15, 75))
    graph = signed_graph(100, len(palette) + 2 * len(blocks) + 1)
    terms = graph_subdivision(pairs, graph, palette)
    rebuilt = {}
    for value, edge_pairs in terms:
        rebuilt = add(rebuilt, lift(d, zero, blocks, edge_pairs, palette), value)
    assert rebuilt == lift(d, zero, blocks, pairs, palette)
    counts['fixed_palette_path_telescoping'] += 1
    counts['path_frame_terms_checked'] = len(terms)
    wrong = add(rooted_difference(2, 6, 7, (1, 2)),
                rooted_difference(2, 7, 8, (3, 4)))
    assert wrong != rooted_difference(2, 6, 8, (1, 2))
    assert not signature(wrong, 2)
    counts['incoherent_palette_negative_control'] += 1
    z = (1, 1, 2)
    cube = raw_product(((1, 3), (1, 4), (2, 5)))
    assert (1, 1, 5) in cube
    assert cell_type(z)[0] == cell_type((1, 1, 5))[0]
    counts['nontriangular_singleton_negative_control'] += 1
    for d in (5, 6):
        a, s, ca, cs = invoices(d)
        P = ca[d] + d * max(a[b] - 1 for b in range(1, d + 1))
        S = max(cs.values()) * (2 * max(s.values())) ** d
        T = [1]
        for j in range(1, d + 1):
            T.append(T[j - 1] + sum(comb(j - 1, b - 1) * 2 ** (b - 1) * T[j - b]
                                   for b in range(1, j + 1)))
        assert T[d] <= (2 * d + 1) ** d
        assert P > 0 and S >= 2 ** d
        print({'dimension': d, 'palette_size': P, 'template_support_bound': S,
               'type_count': T[d], 'absorber_coefficient_log2_bound':
               (2 * T[d]).bit_length() + T[d] * (1 + 2 * S).bit_length()})
        counts['symbolic_dimension_ledgers'] += 1
    print(dict(sorted(counts.items())))
    print('AF finite controls passed; no prime-array certificate was produced.')


if __name__ == '__main__':
    run()

