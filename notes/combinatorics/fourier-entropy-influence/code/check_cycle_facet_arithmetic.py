#!/usr/bin/env python3
"""Exact finite certificates for positive_treewidth_two_arithmetic.md.

Standard library only. The Barahona--Mahjoub facet theorem is an external
mathematical dependency, not a result established by these finite checks.
"""
from itertools import product
import random


def walsh(values):
    a = list(values)
    step = 1
    while step < len(a):
        for first in range(0, len(a), 2 * step):
            for j in range(first, first + step):
                u, v = a[j], a[j + step]
                a[j], a[j + step] = u + v, u - v
        step *= 2
    return a


def cycle_normal_form(s, length, odd_edges):
    u = [((s >> i & 1) ^ (s >> ((i + 1) % length) & 1)
          ^ (odd_edges >> i & 1)) for i in range(length)]
    mapped = sum(u[i] << i for i in range(length - 1))
    mapped |= (s & 1) << (length - 1)
    return mapped, sum(u) == 1


def check_normal_forms():
    maps = points = 0
    for length in range(3, 9):
        for F in range(1 << length):
            if F.bit_count() % 2 == 0:
                continue
            images = []
            ground = 0
            for s in range(1 << length):
                mapped, inside = cycle_normal_form(s, length, F)
                images.append(mapped)
                assert inside == ((mapped & ((1 << (length - 1)) - 1)).bit_count() <= 1)
                ground += inside
                points += 1
            assert len(set(images)) == 1 << length
            assert ground == 2 * length
            maps += 1
    print('Cycle affine normal forms:', maps, 'point checks:', points, flush=True)


def check_modular_lifting():
    tested = eligible = 0
    for n in (3, 4):
        templates = []
        for length in range(3, n + 1):
            for F in range(1 << length):
                if F.bit_count() % 2:
                    outside = [s for s in range(1 << n)
                               if not cycle_normal_form(s, length, F)[1]]
                    templates.append(outside)
        for values in product((-1, 1), repeat=1 << n):
            W = walsh(values)
            for p in (3, 5):
                for outside in templates:
                    tested += 1
                    if all(W[s] % p == 0 for s in outside):
                        eligible += 1
                        assert all(W[s] == 0 for s in outside)
    # Exact noncycle-facet obstruction, including positivity and nonfactorization.
    truth = [1 if x.bit_count() >= 3 else -1 for x in range(16)]
    W = walsh(truth)
    assert W == [-6,-6,-6,2,-6,2,2,2,-6,2,2,2,2,2,2,-6]
    D = {s for s in range(16) if s.bit_count() in (2, 3)}
    assert all(W[s] % 3 == 0 and W[s] != 0 for s in range(16) if s not in D)
    assert all(W[s] % 3 for s in D)
    val3 = [int(abs(a) == 6) for a in W]
    for i in range(4):
        for s in range(16):
            if s >> i & 1:
                val3[s] -= val3[s ^ (1 << i)]
    assert any(c and s.bit_count() >= 3 for s, c in enumerate(val3))
    print('Boolean modular tests:', tested, 'eligible exact lifts:', eligible,
          'primes: 3,5; K5-facet failure verified.', flush=True)


def components(vertices, edges):
    adj = {v: set() for v in vertices}
    for u, v in edges:
        if u in adj and v in adj:
            adj[u].add(v)
            adj[v].add(u)
    result = []
    unseen = set(vertices)
    while unseen:
        seed = min(unseen)
        found = {seed}
        todo = [seed]
        unseen.remove(seed)
        while todo:
            v = todo.pop()
            for u in adj[v] & unseen:
                unseen.remove(u)
                found.add(u)
                todo.append(u)
        result.append(found)
    return result


def forest_and_edge_components(vertices, edges):
    blocks = components(vertices, edges)
    edge_counts = [sum(u in B and v in B for u, v in edges) for B in blocks]
    forest = all(m == len(B) - 1 for m, B in zip(edge_counts, blocks))
    return forest, sum(m > 0 for m in edge_counts)


def fundamental_cycles(vertices, edges):
    adj = {v: [] for v in vertices}
    for u, v in edges:
        if u in adj and v in adj:
            adj[u].append(v)
            adj[v].append(u)
    seen, parent, depth = set(), {}, {}
    cycles = []

    def dfs(v, p):
        seen.add(v)
        parent[v] = p
        depth[v] = 0 if p is None else depth[p] + 1
        for u in adj[v]:
            if u == p:
                continue
            if u not in seen:
                dfs(u, v)
            elif depth[u] < depth[v]:
                C = {u}
                w = v
                while w != u:
                    C.add(w)
                    w = parent[w]
                cycles.append(C)

    for v in sorted(vertices):
        if v not in seen:
            dfs(v, None)
    return cycles


def cactus_cutset(vertices, edges):
    """Implement the proof by freezing a forest beside each chosen cycle cut."""
    active = set(vertices)
    K, witnesses = set(), []
    while True:
        cycles = fundamental_cycles(active, edges)
        if not cycles:
            break
        selected = None
        for C in cycles:
            for v in sorted(C):
                blocks = components(active - {v}, edges)
                Q = next(B for B in blocks if next(iter(C - {v})) in B)
                if C - {v} <= Q and forest_and_edge_components(Q, edges) == (True, 1):
                    selected = v, Q
                    break
            if selected:
                break
        assert selected is not None
        v, Q = selected
        K.add(v)
        witnesses.append(Q)
        active -= Q | {v}
    forest, b = forest_and_edge_components(set(vertices) - K, edges)
    assert forest and b >= len(K)
    final = components(set(vertices) - K, edges)
    assert all(Q in final for Q in witnesses)
    assert len(witnesses) == len(K)
    return K, b


def check_cacti():
    rng = random.Random(20261116)
    examples = cuts = 0
    for trial in range(200):
        vertices, edges = {0}, set()
        next_vertex = 1
        for block in range(1 + trial % 30):
            anchor = rng.choice(sorted(vertices))
            length = rng.choice((2, 3, 3, 4, 5, 7))
            new = list(range(next_vertex, next_vertex + length - 1))
            next_vertex += length - 1
            vertices.update(new)
            path = [anchor, *new]
            for u, v in zip(path, path[1:]):
                edges.add(tuple(sorted((u, v))))
            if length >= 3:
                edges.add(tuple(sorted((path[-1], anchor))))
        K, b = cactus_cutset(vertices, edges)
        examples += 1
        cuts += len(K)
    print('Constructed cactus graphs:', examples, 'total certified cuts:', cuts,
          'fixed seed: 20261116', flush=True)


def check_graph_only_barrier():
    n = 11
    vertices = set(range(n))
    edges = {(i, j) for i in range(n) for j in range(i + 1, min(n, i + 3))}
    # Bags {i,i+1,i+2} give width two. Check every nonempty feedback set.
    gaps = []
    for mask in range(1, 1 << n):
        K = {i for i in range(n) if mask >> i & 1}
        forest, b = forest_and_edge_components(vertices - K, edges)
        if forest:
            gaps.append(len(K) - 1 - b)
    assert min(gaps) == 1
    print('P_11 squared:', 2**n - 1, 'cutsets enumerated;', len(gaps),
          'feedback sets; minimum k-1-b:', min(gaps), flush=True)


if __name__ == '__main__':
    check_normal_forms()
    check_modular_lifting()
    check_cacti()
    check_graph_only_barrier()
    print('All exact finite checks passed; the universal proofs are in the manuscript.')
