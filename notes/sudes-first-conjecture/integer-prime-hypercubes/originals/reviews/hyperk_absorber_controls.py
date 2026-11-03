#!/usr/bin/env python3
"""Independent exact controls for AF and the BK rounding/lifting interface.

No author module is imported. A finite full absorber replay is not an
asymptotic proof, a prime-array certificate, or verification of UF sampling.
"""
from collections import Counter, defaultdict, deque
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, product
from math import comb, gcd
from pathlib import Path
from random import Random
import argparse
import json

REVISION = 'c7f22dd8a01d28ab02c832f6c2b8b4145d88b6bb'
BINDINGS = {
 'manuscripts/hyperk_reconstruction_alt.md':'623cae1101615723a9ddc367145675c41d93067ee64502663b56d072059eeeb5',
 'code/hyperk_reconstruction_alt.py':'ab974d038fcc852645d3af0020ff2be47f93adfb847b8c2f95327a0f53b76060',
 'manuscripts/hyperk_distributed_kernel.md':'a0ea6e14b51b2cdd92b4c9da442f1fef3eeeafa26cf3ef3f84dd4290f9c6ac27',
 'code/hyperk_distributed_kernel.py':'b05dc1078ba84f7969898abd6d6444249b12d953df0a8fd7316abae0e2535e8a',
 'manuscripts/hyperk_full_controller.md':'38de54de8b5e5d751e9d700f689b9417b610019d56e170d47f209c86e2adbec6',
 'manuscripts/hyperk_kernel_research.md':'c4dc2db4da2e502f0bc8d564e44c2f504b13e9e0fae7ae77b780cfdb70838f44',
 'code/hyperk_kernel_research.py':'4c96f78d90110752293dc798059f87c091b7d6578ea63c0734cc3541d3d2cc34',
 'manuscripts/hyperk_incidence.md':'fd2ab35b539415ac65a132b7fddfb6acaa87b5af65f579f9eb64f27cc7e403d8',
 'code/hyperk_incidence.py':'8b2bbd2e88fdbfeb5461f6b85e1bd39626df8d4b6caa0818816aff99bd47283e',
}


def add(a, b, scale=1):
    out = dict(a)
    for x, value in b.items():
        out[x] = out.get(x, 0)+scale*value
        if not out[x]: del out[x]
    return out


def l1(a): return sum(abs(x) for x in a.values())


def box(pairs):
    assert all(u != v for u, v in pairs)
    return {tuple(pairs[i][bit] for i, bit in enumerate(bits)):(-1)**sum(bits)
            for bits in product((0, 1), repeat=len(pairs))}


def tensor(factors, d):
    out = {(None,)*d:1}
    for coordinates, factor in factors:
        nxt = {}
        for x, a in out.items():
            for y, b in factor.items():
                z = list(x)
                for i, v in zip(coordinates, y):
                    assert z[i] is None
                    z[i] = v
                z = tuple(z)
                assert z not in nxt
                nxt[z] = a*b
        out = nxt
    assert all(None not in x for x in out)
    return out


def line_keys(point):
    d = len(point)
    for r in range(1, d+1):
        for block in combinations(range(d), r):
            t = point[block[0]]
            if not t:
                if any(point[i] for i in block): continue
                signs = ((1,)+s for s in product((-1, 1), repeat=r-1))
            elif any(abs(point[i]) != abs(t) for i in block): continue
            else: signs = (tuple(point[i]//t for i in block),)
            fixed = tuple((i, point[i]) for i in range(d) if i not in block)
            for sign in signs: yield block, sign, fixed


def image(a):
    sums = defaultdict(int)
    for point, value in a.items():
        for key in line_keys(point): sums[key] += value
    return {key:value for key, value in sums.items() if value}


def margins(a):
    sums = defaultdict(int)
    for x, value in a.items():
        for i in range(len(x)): sums[i, x[:i]+x[i+1:]] += value
    return {key:value for key, value in sums.items() if value}


def pairable(a):
    assert set(a.values()) <= {-1, 1} and not margins(a)
    if not a: return
    for axis in range(len(next(iter(a)))):
        fibers = defaultdict(Counter)
        for x, value in a.items(): fibers[x[:axis]+x[axis+1:]][value] += 1
        assert all(v[1] == v[-1] for v in fibers.values())


def collections(left, limit, signed):
    if not left:
        yield ()
        return
    first, rest = left[0], left[1:]
    yield from collections(rest, limit, signed)
    for size in range(2, min(limit, len(left))+1):
        for tail in combinations(rest, size-1):
            block = (first,)+tail
            remaining = tuple(x for x in rest if x not in tail)
            signs = [(1,)+t for t in product((-1, 1), repeat=size-1)] if signed else [(1,)*size]
            for sign in signs:
                for after in collections(remaining, limit, signed):
                    yield ((block, sign),)+after


@lru_cache(None)
def pure(d):
    if d == 1: return {(1,):1}, 1
    bank, next_label = {}, d+2
    for size in range(2, d):
        for block in combinations(range(d), size):
            child, count = pure(size)
            bank[block] = {tuple(next_label+v-1 for v in x):a for x, a in child.items()}
            next_label += count
    out = {}
    for partition in collections(tuple(range(d)), d-1, False):
        covered = set(i for block, _ in partition for i in block)
        factors = [(block, bank[block]) for block, _ in partition]
        factors += [((i,), {(1,):1, (i+2,):-1}) for i in range(d) if i not in covered]
        term = tensor(factors, d)
        assert set(out).isdisjoint(term)
        out = add(out, term, (-1)**len(partition))
    return out, next_label-1


@lru_cache(None)
def central_raw(d):
    if d == 0: return {():1}, 0
    bank, next_label = {}, d+1
    for size in range(2, d+1):
        for block in combinations(range(d), size):
            for tail in product((-1, 1), repeat=size-1):
                sign = (1,)+tail
                child, count = pure(size)
                bank[block, sign] = {tuple(s*(next_label+v-1) for s, v in zip(sign, x)):a
                                     for x, a in child.items()}
                next_label += count
    out = {}
    for partition in collections(tuple(range(d)), d, True):
        covered = set(i for block, _ in partition for i in block)
        factors = [(block, bank[block, sign]) for block, sign in partition]
        factors += [((i,), {(0,):1, (i+1,):-1}) for i in range(d) if i not in covered]
        term = tensor(factors, d)
        assert set(out).isdisjoint(term)
        out = add(out, term, (-1)**len(partition))
    return out, next_label-1


def rooted(d, t, auxiliaries, signs=None):
    signs = signs or (1,)*d
    raw, count = pure(d)
    assert t and abs(t) not in auxiliaries and len(auxiliaries) >= count-1
    return {tuple(s*(t if v == 1 else auxiliaries[v-2]) for s, v in zip(signs, x)):a
            for x, a in raw.items()}


def difference(d, u, v, auxiliaries, signs=None):
    assert u != v
    return add(rooted(d, u, auxiliaries, signs), rooted(d, v, auxiliaries, signs), -1)


def point_type(x):
    zero = tuple(i for i, value in enumerate(x) if not value)
    groups = defaultdict(list)
    for i, value in enumerate(x):
        if value: groups[abs(value)].append(i)
    blocks, parameters = [], []
    for block in sorted(groups.values(), key=lambda b:b[0]):
        t = x[block[0]]
        blocks.append((tuple(block), tuple(x[i]//t for i in block)))
        parameters.append(t)
    return (zero, tuple(blocks)), tuple(parameters)


def generic_pairs(pairs):
    used = set()
    for u, v in pairs:
        current = {abs(u), abs(v)}
        if not u or not v or u == v or used & current: return False
        used |= current
    return True


def lift(d, typ, pairs, palette):
    zero, blocks = typ
    assert generic_pairs(pairs) and len(blocks) == len(pairs)
    assert not ({abs(t) for pair in pairs for t in pair} & set(palette))
    factors, offset = [], 0
    if zero:
        raw, size = central_raw(len(zero))
        local = {tuple(0 if not v else (1 if v > 0 else -1)*palette[abs(v)-1]
                       for v in x):a for x, a in raw.items()}
        factors.append((zero, local))
        offset += size
    for (block, sign), (u, v) in zip(blocks, pairs):
        size = pure(len(block))[1]-1
        factors.append((block, difference(len(block), u, v, palette[offset:offset+size], sign)))
        offset += size
    assert offset <= len(palette)
    return tensor(factors, d)


def generic_decompose(initial, p, m):
    assert not margins(initial)
    assert all(all(x) and len(set(map(abs, x))) == p for x in initial)
    assert m >= 2**(p+1)*p*p
    left, terms, history = dict(initial), [], [l1(initial)]
    while left:
        weights = Counter()
        for x, value in left.items():
            for orbit in map(abs, x): weights[orbit] += abs(value)
        # Independent deterministic choice: the p least-loaded orbit labels
        # have total load at most p^2 ||left||_1 / m.
        anchors = tuple(sorted(range(1, m+1), key=lambda a:(weights[a], a))[:p])
        bad = sum(abs(v) for x, v in left.items() if set(map(abs, x)) & set(anchors))
        assert 2**p*bad <= Fraction(l1(left), 2)
        nxt = dict(left)
        for x, value in left.items():
            if set(map(abs, x)).isdisjoint(anchors):
                pairs = tuple(zip(x, anchors))
                assert generic_pairs(pairs)
                terms.append((value, pairs))
                nxt = add(nxt, box(pairs), -value)
        assert l1(nxt)*2 <= l1(left) and not margins(nxt)
        assert all(all(x) and len(set(map(abs, x))) == p for x in nxt)
        left = nxt
        history.append(l1(left))
    assert sum(abs(c) for c, _ in terms) <= 2*l1(initial)
    rebuilt = {}
    for c, pairs in terms: rebuilt = add(rebuilt, box(pairs), c)
    assert rebuilt == initial
    return terms, history


def partitions(left):
    if not left:
        yield ()
        return
    for size in range(1, len(left)+1):
        for tail in combinations(left[1:], size-1):
            block = (left[0],)+tail
            rest = tuple(i for i in left[1:] if i not in tail)
            for after in partitions(rest): yield (block,)+after


def all_types(d):
    out = []
    for z in range(d+1):
        for zero in combinations(range(d), z):
            remaining = tuple(i for i in range(d) if i not in zero)
            for partition in partitions(remaining):
                choices = [tuple((1,)+tail for tail in product((-1, 1), repeat=len(b)-1))
                           for b in partition]
                for signs in product(*choices):
                    out.append((zero, tuple(zip(partition, signs))))
    return sorted(out, key=lambda typ:(len(typ[1]), typ))


def signed_graph(m, radius):
    graph = {x:set() for x in range(-m, m+1) if x}
    for a in range(1, m+1):
        graph[a].add(-a); graph[-a].add(a)
        for j in range(1, radius+1):
            b = 1+(a-1+j) % m
            if a == b: continue
            for sign in (-1, 1):
                graph[sign*a].add(sign*b); graph[sign*b].add(sign*a)
    return graph


def path(graph, u, v, forbidden):
    assert abs(u) not in forbidden and abs(v) not in forbidden
    prior, queue = {u:None}, deque([u])
    while queue:
        x = queue.popleft()
        if x == v: break
        for y in sorted(graph[x]):
            if abs(y) not in forbidden and y not in prior:
                prior[y] = x; queue.append(y)
    assert v in prior
    out = [v]
    while out[-1] != u: out.append(prior[out[-1]])
    out.reverse()
    assert len(out) == len(set(out))
    return out


def subdivide(pairs, graph, palette):
    terms = [(1, pairs)]
    for i in range(len(pairs)):
        nxt = []
        for coefficient, current in terms:
            forbidden = set(palette)
            for j, edge in enumerate(current):
                if i != j: forbidden.update(map(abs, edge))
            walk = path(graph, *current[i], forbidden)
            for u, v in zip(walk, walk[1:]):
                edge = tuple(sorted((u, v)))
                value = coefficient*(1 if edge == (u, v) else -1)
                item = current[:i]+(edge,)+current[i+1:]
                assert generic_pairs(item)
                nxt.append((value, item))
        terms = nxt
    counts = Counter(edges for _, edges in terms)
    assert max(counts.values(), default=0) <= 1
    return terms


def matrix_mul(a, b):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def incidence_matrix(n):
    points = list(product(range(-n//2+1, n//2+1), repeat=2))
    assert len(points) == n*n
    keys = sorted(set(key for point in points for key in line_keys(point)))
    rows = [[int(key in set(line_keys(point))) for point in points] for key in keys]
    assert len(rows) == 2*n+2
    return points, rows


def unit_elimination(a):
    a = [row[:] for row in a]
    original = [row[:] for row in a]
    nr, nc = len(a), len(a[0])
    u = [[int(i == j) for j in range(nr)] for i in range(nr)]
    q = [[int(i == j) for j in range(nc)] for i in range(nc)]
    qi = [[int(i == j) for j in range(nc)] for i in range(nc)]
    rank = 0
    while rank < min(nr, nc):
        candidate = next(((i, j) for i in range(rank, nr) for j in range(rank, nc)
                          if abs(a[i][j]) == 1), None)
        if candidate is None: break
        i, j = candidate
        a[rank], a[i] = a[i], a[rank]; u[rank], u[i] = u[i], u[rank]
        for row in a: row[rank], row[j] = row[j], row[rank]
        for row in q: row[rank], row[j] = row[j], row[rank]
        qi[rank], qi[j] = qi[j], qi[rank]
        if a[rank][rank] == -1:
            a[rank] = [-x for x in a[rank]]; u[rank] = [-x for x in u[rank]]
        for i in range(nr):
            if i == rank: continue
            coefficient = a[i][rank]
            a[i] = [x-coefficient*y for x, y in zip(a[i], a[rank])]
            u[i] = [x-coefficient*y for x, y in zip(u[i], u[rank])]
        for j in range(nc):
            if j == rank: continue
            coefficient = a[rank][j]
            if not coefficient: continue
            for row in a: row[j] -= coefficient*row[rank]
            for row in q: row[j] -= coefficient*row[rank]
            qi[rank] = [x+coefficient*y for x, y in zip(qi[rank], qi[j])]
        rank += 1
    assert matrix_mul(matrix_mul(u, original), q) == a
    assert matrix_mul(q, qi) == [[int(i == j) for j in range(nc)] for i in range(nc)]
    return a, q, qi, rank


def lattice_controls():
    points, a = incidence_matrix(9)
    diagonal, q, qi, rank = unit_elimination(a)
    assert rank == 19 and all(not any(row) for row in diagonal[rank:])
    rng = Random(2026110307)
    coefficients = [rng.randint(-3, 3) for _ in range(len(points)-rank)]
    values = [sum(row[rank+j]*v for j, v in enumerate(coefficients)) for row in q]
    initial = {p:v for p, v in zip(points, values) if v}
    assert not image(initial)
    lifts = 0
    for modulus in (1, 2, 3, 4, 6, 8, 9, 12, 15, 30):
        free = [rng.randrange(modulus) for _ in range(len(points)-rank)]
        exact = [sum(row[rank+j]*v for j, v in enumerate(free)) for row in q]
        representatives = [x % modulus for x in exact]
        assert all(sum(x*y for x, y in zip(row, representatives)) % modulus == 0 for row in a)
        assert not image({p:v for p, v in zip(points, exact) if v})
        assert all((x-y) % modulus == 0 for x, y in zip(exact, representatives))
        lifts += 1
    # Stable saturation cannot be silently transferred to n=3.
    small_points, small = incidence_matrix(3)
    reduced, change, inverse, unit_rank = unit_elimination(small)
    assert unit_rank == 6
    tail = next(row for row in reduced[unit_rank:] if any(row))
    divisor = 0
    for x in tail: divisor = gcd(divisor, x)
    assert divisor == 3
    primitive = [x//divisor for x in tail]
    j = next(j for j in range(unit_rank, len(primitive)) if primitive[j] % 3)
    witness = [row[j] % 3 for row in change]
    assert all(sum(x*y for x, y in zip(row, witness)) % 3 == 0 for row in small)
    transformed = [sum(x*y for x, y in zip(row, witness)) for row in inverse]
    assert sum(x*y for x, y in zip(primitive, transformed)) % 3 != 0
    return initial, {'stable_unit_rank':rank, 'composite_lifts':lifts,
                     'small_order_unit_rank':unit_rank, 'small_order_nonliftable_modulus':3}


def absorb_two(initial, m=90):
    d, P, H = 2, 12, 5
    assert m >= 66 and not image(initial)
    palettes = [tuple(range(1+j*P, 1+(j+1)*P)) for j in range(H)]
    graph = signed_graph(m, P+2*d+1)
    left, compact, norms = dict(initial), [], [l1(initial)]
    for typ in all_types(d):
        restriction = {parameters:value for x, value in left.items()
                       for current, parameters in [point_type(x)] if current == typ}
        p = len(typ[1])
        assert not margins(restriction)
        if not restriction: continue
        terms = [(restriction[()], ())] if p == 0 else generic_decompose(restriction, p, m)[0]
        for coefficient, pairs in terms:
            endpoint_orbits = {abs(x) for edge in pairs for x in edge}
            index = next(i for i, palette in enumerate(palettes) if endpoint_orbits.isdisjoint(palette))
            value = lift(d, typ, pairs, palettes[index])
            assert not image(value)
            pairable(value)
            for x in value:
                actual_type, parameters = point_type(x)
                assert actual_type == typ or len(parameters) > p
            compact.append((coefficient, typ, index, pairs))
            left = add(left, value, -coefficient)
        assert not any(point_type(x)[0] == typ for x in left)
        assert not image(left)
        norms.append(l1(left))
    assert not left
    cost = sum(abs(c) for c, _, _, _ in compact)
    coefficients = Counter()
    expanded_terms = 0
    for c, typ, palette_index, pairs in compact:
        terms = subdivide(pairs, graph, palettes[palette_index])
        expanded_terms += len(terms)
        for sign, edges in terms: coefficients[typ, palette_index, edges] += c*sign
    assert max(map(abs, coefficients.values()), default=0) <= cost
    rebuilt, occupancy = {}, Counter()
    for (typ, index, edges), coefficient in coefficients.items():
        value = lift(d, typ, edges, palettes[index])
        rebuilt = add(rebuilt, value, coefficient)
        occupancy.update(value.keys())
    assert rebuilt == initial
    return {'input_l1':l1(initial), 'stratum_norms':norms, 'compact_lifts':len(compact),
            'compact_absolute_coefficient_cost':cost, 'expanded_terms':expanded_terms,
            'used_indexed_frame_members':len(coefficients),
            'maximum_coefficient':max(map(abs, coefficients.values()), default=0),
            'used_frame_point_degree':max(occupancy.values(), default=0)}


def local_controls():
    counts = Counter()
    for d in range(1, 5):
        _, a = pure(d)
        auxiliaries = tuple(range(20, 20+a-1))
        signs = (1,)+tuple((-1)**i for i in range(1, d))
        for u, v in ((1, 2), (-1, -2), (1, -1), (-2, 3)):
            q = rooted(d, u, auxiliaries, signs)
            assert image(q) == {(tuple(range(d)), signs, ()):1}
            delta = difference(d, u, v, auxiliaries, signs)
            assert not image(delta)
            assert all(any(abs(x) not in auxiliaries for x in point) for point in delta)
            pairable(delta)
            counts['rooted_endpoint_controls'] += 1
    for d in (1, 2, 3):
        c, _ = central_raw(d)
        assert c[(0,)*d] == 1 and not image(c)
        pairable(c)
        counts['central_controls'] += 1
    # Dense generic cycles force a genuine bad-anchor remainder before stopping.
    m = 64
    cycle = {(i, 1+i % m):1 for i in range(1, m+1)}
    for i in range(1, m+1): cycle[i, 1+(i+1) % m] = -1
    _, history = generic_decompose(cycle, 2, m)
    assert len(history) >= 3
    counts['generic_contraction_steps'] = len(history)-1
    # A fixed simple path rule telescopes exactly and has unique final tuples.
    graph = signed_graph(55, 7)
    palette = (1, 2)
    pairs = ((6, -28), (15, 45))
    terms = subdivide(pairs, graph, palette)
    rebuilt = {}
    for coefficient, edge_pairs in terms: rebuilt = add(rebuilt, box(edge_pairs), coefficient)
    assert rebuilt == box(pairs)
    counts['unique_prefix_path_terms'] = len(terms)
    # A non-simple walk can telescope but violates the unit multiplicity bound.
    walk = (6, 7, 8, 6, 7, 8, 6, 9)
    repeated = Counter()
    for u, v in zip(walk, walk[1:]):
        edge = tuple(sorted((u, v)))
        repeated[edge] += 1 if edge == (u, v) else -1
    assert max(map(abs, repeated.values())) == 2
    counts['nonsimple_path_negative'] += 1
    wrong = add(difference(2, 6, 7, (1, 2)), difference(2, 7, 8, (3, 4)))
    assert wrong != difference(2, 6, 8, (1, 2)) and not image(wrong)
    counts['incoherent_palette_negative'] += 1
    first = difference(2, 6, 7, (1, 2))
    generic_part = {x:v for x, v in first.items() if len(set(map(abs, x))) == 2}
    assert margins(generic_part)
    counts['premature_stratum_negative'] += 1
    # Zero axes and zero full-body traces do not imply the full signed kernel.
    body_only_false_positive = box(((1, 2), (1, 3), (4, 5)))
    signature = image(body_only_false_positive)
    assert not margins(body_only_false_positive) and signature
    assert all(len(key[0]) == 2 for key in signature)
    counts['body_only_kernel_negative'] += 1
    # Fixed-frame point degree, including every indexed template in the fixture.
    edges = [(i, 1+i % 7) for i in range(1, 8)]
    edges += [(-u, -v) for u, v in edges]+[(i, -i) for i in range(1, 8)]
    typ = ((), (((0, 1), (1, -1)), ((2,), (1,))))
    occupancy = Counter()
    total = 0
    for e, f in product(edges, repeat=2):
        if not generic_pairs((e, f)): continue
        value = lift(3, typ, (e, f), (20, 21))
        assert not image(value)
        occupancy.update(value.keys()); total += 1
    assert max(occupancy.values()) <= (2*3)*3
    counts['fixed_frame_members'] = total
    counts['fixed_frame_point_degree'] = max(occupancy.values())
    # BK coefficient rounding and integer absorber composition.
    ab, bc, ac = [difference(2, *ends, (20, 21)) for ends in ((6, 7), (7, 8), (6, 8))]
    assert add(add(ab, bc), ac, -1) == {}
    frame = [ab, bc, ac]
    real_coefficients = [Fraction(7, 2), Fraction(-5, 2), Fraction(1, 2)]
    exact, rounded, point_load = {}, {}, Counter()
    for c, template in zip(real_coefficients, frame):
        exact = add(exact, template, c)
        rounded = add(rounded, template, (c+Fraction(1, 2)).numerator//(c+Fraction(1, 2)).denominator)
        point_load.update(template.keys())
    assert all(v.denominator == 1 for v in exact.values())
    residual = add(exact, rounded, -1)
    assert residual and not image(residual)
    assert max(map(abs, residual.values())) <= Fraction(max(point_load.values()), 2)
    residue_replay = absorb_two({x:int(v) for x, v in residual.items()})
    counts['rounding_then_absorber'] += 1
    # A nonintegral real input has a close integer kernel point by coefficient
    # rounding; rounding its cells with the same tie rule destroys its margins.
    real_input = {x:Fraction(v, 2) for x, v in ab.items()}
    assert not image(real_input) and not image(ab)
    assert max(abs(real_input[x]-ab[x]) for x in ab) == Fraction(1, 2)
    wrong_cells = {x:1 for x, v in real_input.items() if v > 0}
    assert image(wrong_cells)
    counts['real_covering_radius_control'] += 1
    counts['entrywise_rounding_negative'] += 1
    return dict(counts), history, residue_replay


def main(source):
    root = source/'problems'/'prime-arrays-beyond-square'
    for path, digest in BINDINGS.items():
        assert sha256((root/path).read_bytes()).hexdigest() == digest, path
    initial, lattice = lattice_controls()
    replay = absorb_two(initial)
    local, history, rounding = local_controls()
    print(json.dumps({'source_revision':REVISION, 'source_bindings':len(BINDINGS),
                      'lattice':lattice, 'full_absorber_replay':replay,
                      'local_controls':local, 'generic_norm_history':history,
                      'rounding_absorber_replay':rounding,
                      'scope':'exact finite independent controls; UF probability and prime arrays are not certified'},
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source_archive', type=Path)
    main(parser.parse_args().source_archive)
