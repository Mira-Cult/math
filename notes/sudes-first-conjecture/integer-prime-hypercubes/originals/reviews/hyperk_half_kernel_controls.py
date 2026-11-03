#!/usr/bin/env python3
"""Independent finite controls for the frozen half-coordinate kernel review.

No author module is imported. These exact checks do not prove an asymptotic
threshold, certify a path as an expander, or produce a full prime array.
"""
from collections import Counter, defaultdict, deque
from itertools import combinations, product
from hashlib import sha256
from math import isqrt
from pathlib import Path
from random import Random
import argparse
import json

REVISION = 'f9697734c0c1d87eb8ab8af4051d0e8495ac9b56'
BINDINGS = {
    'manuscripts/hyperk_half.md': '0a15b37c530754a70f4b42ac410445c88532b0c6f28856bedf5ac280ee09afbe',
    'code/hyperk_half.py': '2ba335cb46208f3597a8aeff619ceb62f6661eaac57738cab92cb08eb727201c',
    'manuscripts/hyperk_controller.md': 'bcccf122f966daf70101bfff1f4cf00cfc9559c68c5097d80c981ae405cf1f23',
    'manuscripts/incidence.md': '2c9e334928fbadffa703ad2baebbcabd3049a3c356037805526565d8256b53e5',
    'manuscripts/hyper4_axis.md': 'ca9cefea5142343144dfa27904279066743d67e7f79a4c763ff0fc3ab45e4496',
}


def add(a, b, c=1):
    for p, v in b.items():
        a[p] = a.get(p, 0) + c*v
        if not a[p]:
            del a[p]
    return a


def box(pairs):
    assert all(a != b for a, b in pairs)
    return {tuple(pairs[i][bit] for i, bit in enumerate(bits)):
            (-1)**sum(bits) for bits in product((0, 1), repeat=len(pairs))}


def selector(labels, pattern):
    assert len(labels) == len(pattern)+1
    assert min(labels) > 0 and len(set(labels)) == len(labels)
    assert pattern[0] == 1
    return box(tuple((s*labels[0], s*b) for s, b in zip(pattern, labels[1:])))


def line_keys(point):
    """All full signed-coordinate lines through a point, center included.

    Only the direction and fixed coordinates identify a line. The construction
    uses geometric equal-absolute-value membership, not tensor contractions.
    """
    d = len(point)
    for r in range(1, d+1):
        for block in combinations(range(d), r):
            t = point[block[0]]
            if t == 0:
                if any(point[i] for i in block):
                    continue
                patterns = ((1,)+tail for tail in product((-1, 1), repeat=r-1))
            elif any(abs(point[i]) != abs(t) for i in block):
                continue
            else:
                patterns = (tuple(point[i]//t for i in block),)
            fixed = tuple((i, point[i]) for i in range(d) if i not in block)
            for pattern in patterns:
                yield block, pattern, fixed


def image(a):
    out = defaultdict(int)
    for point, value in a.items():
        for key in line_keys(point):
            out[key] += value
    return {key: value for key, value in out.items() if value}


def body(a, d):
    full = tuple(range(d))
    im = image(a)
    return {pattern: im.get((full, pattern, ()), 0)
            for pattern in ((1,)+tail for tail in product((-1, 1), repeat=d-1))}


def body_kernel(a, d, modulus=None):
    for key, value in image(a).items():
        if len(key[0]) in (1, d):
            assert value == 0 if modulus is None else value % modulus == 0


def pairability(a):
    d = len(next(iter(a)))
    assert set(a.values()) <= {-1, 1}
    for i in range(d):
        groups = defaultdict(Counter)
        for p, value in a.items():
            groups[p[:i]+p[i+1:]][value] += 1
        assert all(count[1] == count[-1] for count in groups.values())


def projection_controls():
    cases = 0
    double_trace_rejections = 0
    exemplars = {}
    for d in (2, 3, 4):
        raw_patterns = [((-1, 1),)*d, ((0, 1),)*d,
                        tuple(((-2, 1), (0, 2), (-1, 2))[i % 3] for i in range(d))]
        for factors in raw_patterns:
            raw = box(factors)
            projected = dict(raw)
            used = set(raw)
            next_label = 11
            pieces = 1
            markers = []
            for pattern, trace in body(raw, d).items():
                for _ in range(abs(trace)):
                    marker = selector(tuple(range(next_label, next_label+d+1)), pattern)
                    next_label += d+1
                    assert used.isdisjoint(marker)
                    used.update(marker)
                    add(projected, marker, -1 if trace > 0 else 1)
                    markers.append((marker, 1 if trace > 0 else -1))
                    pieces += 1
            body_kernel(projected, d)
            pairability(projected)
            assert len(projected) == pieces*2**d
            assert pieces <= 1+2**(2*d-1)
            if any(abs(t) == 2 for t in body(raw, d).values()):
                bad = dict(projected)
                add(bad, markers[0][0], markers[0][1])
                assert any(body(bad, d).values())
                double_trace_rejections += 1
            exemplars[d] = projected, pieces
            cases += 1
    return exemplars, cases, double_trace_rejections


def repair_edges(edges, supports, cap):
    use = Counter()
    repaired = []
    for label, (u, v) in enumerate(edges):
        if supports[u].isdisjoint(supports[v]):
            path = (u, v)
        else:
            candidates = [w for w in range(len(supports)) if w not in (u, v)
                          and use[w] < cap and supports[w].isdisjoint(supports[u])
                          and supports[w].isdisjoint(supports[v])]
            assert candidates
            w = min(candidates, key=lambda q: (use[q], q))
            use[w] += 1
            path = (u, w, v)
        for j, (a, b) in enumerate(zip(path, path[1:])):
            assert supports[a].isdisjoint(supports[b])
            repaired.append((label, j, a, b))
    assert max(use.values(), default=0) <= cap
    return repaired


def cut_size(edges, mask):
    return sum(((mask >> u) & 1) != ((mask >> v) & 1) for u, v in edges)


def bounded_integer_flow(edges, demand, cap):
    """Independent integral augmenting-path solver on labeled undirected edges."""
    pending = list(demand)
    flow = [0]*len(edges)
    assert sum(pending) == 0
    while any(x > 0 for x in pending):
        start = next(i for i, x in enumerate(pending) if x > 0)
        parent = {start: None}
        queue = deque([start])
        target = None
        while queue and target is None:
            u = queue.popleft()
            for j, (a, b) in enumerate(edges):
                if a == u:
                    v, direction, capacity = b, 1, cap-flow[j]
                elif b == u:
                    v, direction, capacity = a, -1, cap+flow[j]
                else:
                    continue
                if capacity <= 0 or v in parent:
                    continue
                parent[v] = (u, j, direction, capacity)
                if pending[v] < 0:
                    target = v
                    break
                queue.append(v)
        assert target is not None, 'cut-capacity obstruction'
        path = []
        v = target
        while v != start:
            u, j, direction, capacity = parent[v]
            path.append((j, direction, capacity))
            v = u
        amount = min(pending[start], -pending[target], *(c for _, _, c in path))
        pending[start] -= amount
        pending[target] += amount
        for j, direction, _ in path:
            flow[j] += direction*amount
    assert not any(pending)
    actual = [0]*len(demand)
    for (u, v), f in zip(edges, flow):
        assert abs(f) <= cap
        actual[u] += f
        actual[v] -= f
    assert actual == demand
    return flow


def marker_graph_controls():
    # The first two markers overlap with opposite signs at (1,3): their
    # uncorrected difference really has coefficient -2 there.
    markers = [selector((1, 4, 3), (1, 1)), selector((2, 1, 3), (1, 1))]
    markers += [selector((10+3*j, 11+3*j, 12+3*j), (1, 1)) for j in range(6)]
    supports = [set(a) for a in markers]
    bad = add(dict(markers[0]), markers[1], -1)
    assert bad[(1, 3)] == -2
    body_kernel(bad, 2)
    p = len(markers)
    # Two separately labeled copies of K_8 have cut expansion exactly eight.
    edges = [(u, v) for u, v in combinations(range(p), 2) for _ in range(2)]
    routed = repair_edges(edges, supports, 128)
    routed_edges = [(u, v) for _, _, u, v in routed]
    degree = Counter(x for edge in routed_edges for x in edge)
    assert max(degree.values()) <= 320
    cuts = 0
    for mask in range(1, (1 << p)-1):
        required = 8*min(mask.bit_count(), p-mask.bit_count())
        old = cut_size(edges, mask)
        new = cut_size(routed_edges, mask)
        assert new >= old >= required
        cuts += 1
    # Erasing parallel labels loses this expansion guarantee.
    unlabeled = set(tuple(sorted(e)) for e in routed_edges)
    assert any(cut_size(unlabeled, mask) < 8*min(mask.bit_count(), p-mask.bit_count())
               for mask in range(1, (1 << p)-1))
    rng = Random(2026110242)
    demands = [[0]*p, [8]*4+[-8]*4]
    for _ in range(60):
        half = [rng.randint(-24, 24) for _ in range(p//2)]
        d = half+[-x for x in half]
        rng.shuffle(d)
        demands.append(d)
    for demand in demands:
        cap = (max(map(abs, demand))+7)//8
        flow = bounded_integer_flow(routed_edges, demand, cap)
        left, right = {}, {}
        for q, value in zip(markers, demand):
            add(left, q, value)
        for (u, v), value in zip(routed_edges, flow):
            add(right, markers[u], value)
            add(right, markers[v], -value)
        assert left == right
    path = [(i, i+1) for i in range(p-1)]
    routed_path = repair_edges(path, supports, 4)
    assert max(Counter(x for _, _, u, v in routed_path for x in (u, v)).values()) <= 10
    residue_cases = 0
    for modulus in (1, 2, 4, 6, 8, 9, 15, 30):
        for _ in range(10):
            demand = [rng.randrange(modulus) for _ in range(p-1)]
            demand.append(-sum(demand) % modulus)
            prefix = []
            partial = 0
            for x in demand[:-1]:
                partial = (partial+x) % modulus
                prefix.append(partial)
            actual = [0]*p
            for label, _, u, v in routed_path:
                actual[u] += prefix[label]
                actual[v] -= prefix[label]
            assert all((a-b) % modulus == 0 for a, b in zip(actual, demand))
            residue_cases += 1
    return {'all_cuts_checked': cuts, 'bounded_integer_flows': len(demands),
            'composite_and_modulus_one_flows': residue_cases,
            'original_labeled_edges': len(edges), 'routed_labeled_edges': len(routed),
            'maximum_routed_degree': max(degree.values()),
            'nonunit_overlap_and_parallel_label_negatives': 2}


def tensor(a, b):
    return {x+y: v*w for x, v in a.items() for y, w in b.items()}


def compound_controls(exemplars):
    cases = 0
    for d, (inner, pieces) in exemplars.items():
        pattern = (1,)+tuple(-1 if i % 2 else 1 for i in range(1, d))
        seen_stages = defaultdict(set)
        intersection_counts = Counter()
        for stage in range(3):
            labels = tuple(range(1000+stage*(d+1), 1000+(stage+1)*(d+1)))
            outer = selector(labels, pattern)
            delta = tensor(outer, inner)
            im = image(delta)
            native = tuple(range(d)), pattern
            for key, value in im.items():
                assert len(key[0]) != 1
                if len(key[0]) >= d:
                    assert key[:2] == native
                    assert value == inner[tuple(x for _, x in key[2])]
            for point in delta:
                for key in line_keys(point):
                    seen_stages[key].add(stage)
                    intersection_counts[(key, stage)] += 1
            pairability(delta)
            cases += 1
        for key, stages in seen_stages.items():
            if key[:2] != native:
                assert len(stages) <= 1
                assert all(intersection_counts[key, s] <= 2*pieces for s in stages)
    # Body kernel is strictly weaker than the full signed-contraction kernel.
    inner = box(((1, 2), (1, 3), (4, 5)))
    body_kernel(inner, 3)
    assert any(len(key[0]) == 2 for key in image(inner))
    outer = selector((20, 21, 22, 23), (1, -1, 1))
    full_image = image(tensor(outer, inner))
    assert any(key[0] == (3, 4) for key in full_image)
    # Dropping the body condition creates another same-size native family.
    bad_inner = selector((1, 2, 3), (1, 1))
    outer2 = selector((20, 21, 22), (1, -1))
    assert any(key[0] == (2, 3) for key in image(tensor(outer2, bad_inner)))
    # Dropping orbit separation creates a forbidden full body even if the
    # complementary factor really is in the complete two-dimensional kernel.
    kernel = add(selector((1, 2, 3), (1, 1)), selector((4, 5, 6), (1, 1)), -1)
    body_kernel(kernel, 2)
    overlapping_outer = selector((1, 8, 9), (1, 1))
    assert image(tensor(overlapping_outer, kernel))[(tuple(range(4)), (1,)*4, ())] == 1
    return {'complete_compound_signatures': cases,
            'scope_body_and_orbit_negatives': 3,
            'whole_bundle_support_range_dimensions': [4, 6, 8]}


def main(source):
    root = source/'problems'/'prime-arrays-beyond-square'
    for path, expected in BINDINGS.items():
        assert sha256((root/path).read_bytes()).hexdigest() == expected, path
    examples, count, negative = projection_controls()
    report = {'source_revision': REVISION, 'source_hashes_checked': len(BINDINGS),
              'independent_projection_signatures': count,
              'omitted_unit_marker_rejections': negative,
              'marker_graph': marker_graph_controls(),
              'compound': compound_controls(examples),
              'scope': 'finite reviewer controls; no asymptotic or full-array certificate'}
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source_archive', type=Path)
    main(parser.parse_args().source_archive)
