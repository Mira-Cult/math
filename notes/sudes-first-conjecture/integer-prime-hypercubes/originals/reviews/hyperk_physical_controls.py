#!/usr/bin/env python3
"""Nonauthor physical controls for the exact frozen all-dimension source.

This program imports no author producer. It verifies source hashes, uses its
own geometry and exact arithmetic, and makes no asymptotic or full-array claim.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from copy import deepcopy
from hashlib import sha256
from fractions import Fraction
from itertools import combinations, product
from math import comb, isqrt, lcm
from pathlib import Path
from random import Random
import json

PREFIX = Path('problems/prime-arrays-beyond-square')
REVISION = '5692d37633ef4b509e8429cddf4ed762e7235d08'
BINDINGS = {
    'manuscripts/hyperk_controller.md': 'bcccf122f966daf70101bfff1f4cf00cfc9559c68c5097d80c981ae405cf1f23',
    'manuscripts/hyperk_cube.md': '98911845eb32e57ef381ad4c6c6e93914b45846f1597747ecef61f7538731eec',
    'manuscripts/hyperk_resources.md': 'c26bd5d67dd3dee746c986c1d11695a4ba92d2aeda53f0e5441b1adf113ce0a7',
    'manuscripts/hyperk_targets.md': '2a69a31ce1a3ecde164bf7748dc52c22b2637551bc97dd821edd497ea9df5306',
    'manuscripts/incidence.md': '2c9e334928fbadffa703ad2baebbcabd3049a3c356037805526565d8256b53e5',
    'manuscripts/hyper4_axis.md': 'ca9cefea5142343144dfa27904279066743d67e7f79a4c763ff0fc3ab45e4496',
    'code/hyperk_controller.py': '150d0d1b3d49bb4c8c134e8cd93622b3cabdc9dd14bd3d11d7f5f3eeb3112965',
    'inputs/hyperk-controller-k5-stage.json': '1c04b2da987fa89d7a7b478c1bac90fcf6d64434f43e6816f570d6d2ba5bb5d0',
    'inputs/hyperk-controller-k6-stage.json': '630938e2c60ad039962ed79d9b0587d8afb0daeada655a67fb3d71e65d35a2b5',
}
HALF_REVISION = 'f9697734c0c1d87eb8ab8af4051d0e8495ac9b56'
HALF_BINDINGS = {
    'manuscripts/hyperk_half.md': '0a15b37c530754a70f4b42ac410445c88532b0c6f28856bedf5ac280ee09afbe',
    'code/hyperk_half.py': '2ba335cb46208f3597a8aeff619ceb62f6661eaac57738cab92cb08eb727201c',
}


def demand(ok, message):
    if not ok:
        raise ValueError(message)


def bind(root, bindings=BINDINGS):
    for name, expected in bindings.items():
        demand(sha256((root/PREFIX/name).read_bytes()).hexdigest() == expected,
               'scientific source hash mismatch: '+name)


def prime(value):
    return (type(value) is int and value >= 2 and
            all(value % d for d in range(2, isqrt(value)+1)))


def directions(k):
    # Independent endpoint-step words, normalized by the first nonzero step.
    for word in product((-1, 0, 1), repeat=k):
        moving = tuple(i for i in range(k) if word[i])
        if moving and word[moving[0]] == 1:
            yield word, moving


def line_inventory(k, n):
    out = set()
    for word, moving in directions(k):
        fixed = [i for i in range(k) if not word[i]]
        for values in product(range(n), repeat=len(fixed)):
            origin = [0 if s >= 0 else n-1 for s in word]
            for i, x in zip(fixed, values):
                origin[i] = x
            out.add(frozenset(tuple(origin[i]+t*word[i] for i in range(k))
                              for t in range(n)))
    return out


def signature(cells, k):
    # Sparse complete images. Line keys use full direction words and fixed data.
    out = Counter()
    for word, moving in directions(k):
        fixed = tuple(i for i in range(k) if not word[i])
        for point, value in cells.items():
            t = point[moving[0]]
            if all(point[i] == t*word[i] for i in moving):
                out[(word, tuple(point[i] for i in fixed))] += value
    return {key: value for key, value in out.items() if value}


def box(factors):
    result = {}
    for bits in product(*(range(len(f)) for f in factors)):
        result[tuple(f[b] for f, b in zip(factors, bits))] = (-1)**sum(bits)
    return result


def add(*terms):
    out = Counter()
    for scalar, tensor in terms:
        for point, value in tensor.items():
            out[point] += scalar*value
    return {point: value for point, value in out.items() if value}


def partial_prime_stage(data):
    demand(data.get('kind') == 'partial-prime-controller', 'scope mismatch')
    k, n, g = data['dimension'], data['order'], data['gap']
    demand(type(k) is int and k >= 2 and type(n) is int and n % 2 == 1,
           'bad dimension/order')
    demand(type(g) is int and g > 0 and g % 2 == 0, 'bad gap')
    before = {}
    for point, value in data['assignments']:
        point = tuple(point)
        demand(len(point) == k and all(type(x) is int and abs(x) <= n//2 for x in point),
               'out of range')
        demand(point not in before, 'cell reused')
        demand(prime(value) and value > 2, 'non-odd-prime entry')
        before[point] = value
    demand(len(set(before.values())) == len(before), 'prime reused')
    demand(sum(prime(x) for x in range(3, max(before.values())+1, 2)) <= n**k,
           'entry outside exact initial pool')
    after = dict(before)
    used = set()
    for left, right in data['switch_pairs']:
        left, right = tuple(left), tuple(right)
        demand(left != right and left in before and right in before, 'invalid edge')
        demand(not (set((left, right)) & used), 'switch endpoint reused')
        demand(abs(before[left]-before[right]) == g, 'unequal actual prime gaps')
        used.update((left, right))
        after[left], after[right] = before[right], before[left]
    demand(used == set(before), 'unpaired entry')
    expected = box(data['factors'])
    actual = {point: after[point]-value for point, value in before.items()}
    demand(actual == {point: g*value for point, value in expected.items()}, 'orientation')
    demand(sorted(before.values()) == sorted(after.values()), 'not a permutation')
    # Unit body fixture: compute all images independently, not its recorded claims.
    images = signature(actual, k)
    bodies = [(key, value) for key, value in images.items() if all(key[0])]
    demand(len(bodies) == 1 and bodies[0][1] == g, 'wrong body trace')
    demand(not any(sum(bool(x) for x in word) == 1 for word, fixed in images),
           'axis was changed')
    return len(before), len(data['switch_pairs'])


def local_load_controls():
    cases = []
    # A path is sufficient for these local incidence counts. No expansion claim.
    n, delta, stages = 5, 2, 3
    edges = [(i, i+1) for i in range(n-1)]
    for k in range(2, 7):
        for d in range(2, k+1):
            native = Counter()
            for outer in product(range(n), repeat=k-d):
                for es in product(edges, repeat=d-1):
                    for point in product(*es):
                        native[point+outer] += stages
            maximum = max(native.values())
            demand(maximum <= delta**(d-1)*stages, 'native point degree')
            # Any signed native line has n points; this is the shadow bound MP.
            for line in line_inventory(k-1, n):
                demand(sum(native[p] for p in line) <= n*delta**(d-1)*stages,
                       'native signed-line shadow bound')
            cases.append(('native', k, d, maximum))
        for d in range(3, k+1):
            r = d-1
            section = Counter()
            outer_total = Counter()
            copies = n**(d-2)
            for outer in product(range(n), repeat=k-d):
                for edge in edges:
                    for endpoint in edge:
                        section[(endpoint,)+outer] += copies*stages
                        outer_total[outer] += copies*stages
            demand(max(section.values()) <= delta*n**(r-1)*stages, 'P1')
            demand(max(outer_total.values()) <= delta*n**r*stages, 'P2')
            cases.append(('aggregate', k, d, max(section.values())))
    # A false degree bound is a rejected numerical claim, not a graph theorem.
    demand(any(row[-1] > stages for row in cases if row[0] == 'native'),
           'degree-one negative control did not fail')
    return cases


def arbitrary_orientation_controls():
    count = 0
    for k in range(2, 7):
        for r in range(k//2+1, k+1):
            if r < 2:
                continue
            for active in combinations(range(k), r):
                for signs in product((-1, 1), repeat=r-1):
                    signs = (1,)+signs
                    factors = [None]*k
                    for j, (i, sign) in enumerate(zip(active, signs)):
                        factors[i] = (sign*20, sign*(21+j))
                    for j, i in enumerate(i for i in range(k) if i not in active):
                        # Zero, reflected and repeated native endpoint patterns.
                        factors[i] = ((0, 1), (-1, 1), (1, 2))[j % 3]
                    image = signature(box(factors), k)
                    native_word = tuple(signs[active.index(i)] if i in active else 0
                                        for i in range(k))
                    demand(any(word == native_word for word, fixed in image), 'lost native image')
                    for word, fixed in image:
                        size = sum(bool(x) for x in word)
                        demand(size != 1, 'axis failure')
                        demand(size < r or word == native_word, 'triangular failure')
                    count += 1
    return count


def obstructions():
    # The common center lies on every normalized body, so this is not a unit selector.
    centered = signature(box([(0, i+1) for i in range(4)]), 4)
    demand(sum(all(word) for word, fixed in centered) == 8, 'center obstruction')
    # At equality, the complementary block is unavoidably an extra native image.
    equal = signature(box([(10, 11), (10, 12), (10, 13),
                           (1, 2), (1, 3), (1, 4)]), 6)
    demand(any(word == (0, 0, 0, 1, 1, 1) for word, fixed in equal),
           'missing equality-boundary spill')
    # Reusing identical pairs is not an odd-dimensional unit-body selector.
    for k in (3, 4, 5, 6):
        image = signature(box([(1, 2)]*k), k)
        demand(image.get(((1,)*k, ()), 0) == 1+(-1)**k, 'false unit selector')
    return 6


def body(values, pattern):
    return sum(value for point, value in values.items()
               if all(point[i] == pattern[i]*point[0] for i in range(len(pattern))))


def margins_zero(values, d, modulus=None):
    for i in range(d):
        total = Counter()
        for point, value in values.items():
            total[point[:i]+point[i+1:]] += value
        demand(all(value == 0 if modulus is None else value % modulus == 0
                   for value in total.values()), 'nonzero axis margin')


def rational_kernel(matrix):
    """An independent exact RREF, only to generate diagnostic integer demands."""
    rows = [[Fraction(x) for x in row] for row in matrix]
    width, pivot_row, pivots = len(rows[0]), 0, []
    for col in range(width):
        nonzero = next((i for i in range(pivot_row, len(rows)) if rows[i][col]), None)
        if nonzero is None:
            continue
        rows[pivot_row], rows[nonzero] = rows[nonzero], rows[pivot_row]
        scale = rows[pivot_row][col]
        rows[pivot_row] = [x/scale for x in rows[pivot_row]]
        for i in range(len(rows)):
            if i != pivot_row and rows[i][col]:
                scale = rows[i][col]
                rows[i] = [x-scale*y for x, y in zip(rows[i], rows[pivot_row])]
        pivots.append(col)
        pivot_row += 1
        if pivot_row == len(rows):
            break
    basis = []
    for free in set(range(width))-set(pivots):
        v = [Fraction(0)]*width
        v[free] = 1
        for i, pivot in enumerate(pivots):
            v[pivot] = -rows[i][free]
        denominator = lcm(*(x.denominator for x in v))
        basis.append([int(x*denominator) for x in v])
    return basis


def interleaved_product(left, right):
    return {tuple(t for pair in zip(a, b) for t in pair): va*vb
            for a, va in left.items() for b, vb in right.items()}


def half_controls():
    reports = []
    signatures = 0
    residue_cases = 0
    scope_failures = 0
    for d in (2, 3, 4):
        patterns = [(1,)+s for s in product((-1, 1), repeat=d-1)]
        raw = [box(f) for f in product(((-1, 0), (0, 1)), repeat=d)]
        trace_matrix = [[body(t, pattern) for t in raw] for pattern in patterns]
        basis = rational_kernel(trace_matrix)
        demand(basis, 'diagnostic trace kernel unexpectedly trivial')
        rng = Random(991000+d)
        weights = [rng.randrange(-9, 10) for _ in basis]
        coefficients = [sum(a*b[j] for a, b in zip(weights, basis))
                        for j in range(len(raw))]
        demand(any(coefficients), 'trivial diagnostic demand')
        target = add(*zip(coefficients, raw))
        margins_zero(target, d)
        demand(all(body(target, pattern) == 0 for pattern in patterns), 'RREF target not in body kernel')

        # All marker alphabets are disjoint in this reconstruction control;
        # the separate cut control below examines intersection rerouting.
        cursor = 3
        markers = []
        groups = {pattern: [] for pattern in patterns}
        attachments = []
        projected = []
        for raw_tensor in raw:
            terms = [(1, raw_tensor)]
            attached = []
            for pattern in patterns:
                trace = body(raw_tensor, pattern)
                for unused in range(abs(trace)):
                    labels = list(range(cursor, cursor+d+1)); cursor += d+1
                    q = box([(s*labels[0], s*labels[i+1]) for i, s in enumerate(pattern)])
                    sign = 1 if trace > 0 else -1
                    index = len(markers)
                    markers.append(q); groups[pattern].append(index)
                    attached.append((index, sign)); terms.append((-sign, q))
            result = add(*terms)
            demand(sum(len(t) for sign, t in terms) == len(result), 'projected support overlap')
            demand(set(result.values()) <= {-1, 1}, 'nonunit projected coefficient')
            margins_zero(result, d)
            demand(all(body(result, pattern) == 0 for pattern in patterns), 'projection trace failure')
            attachments.append(attached); projected.append(result)

        def replay(c, modulus=None):
            actual_target = add(*zip(c, raw))
            charges = [0]*len(markers)
            result = add(*zip([x if modulus is None else x % modulus for x in c], projected))
            for coefficient, attached in zip(c, attachments):
                for index, sign in attached:
                    charges[index] += sign*coefficient
            for pattern, nodes in groups.items():
                total = sum(charges[i] for i in nodes)
                demand(total == 0 if modulus is None else total % modulus == 0, 'incompatible marker sum')
                running = 0
                for u, v in zip(nodes, nodes[1:]):
                    demand(set(markers[u]).isdisjoint(markers[v]), 'overlapping flow pair')
                    running += charges[u]
                    flow = running if modulus is None else running % modulus
                    result = add((1, result), (flow, markers[u]), (-flow, markers[v]))
            difference = add((1, result), (-1, actual_target))
            demand(not difference if modulus is None else
                   all(x % modulus == 0 for x in difference.values()), 'marker reconstruction failure')

        replay(coefficients)
        for modulus in (2, 6, 9, 15):
            c = [x+modulus*((i % 5)-2) for i, x in enumerate(coefficients)]
            replay(c, modulus); residue_cases += 1
        # A source outside the body kernel must fail the exact scalar compatibility.
        bad = [0]*len(raw); bad[0] = 1
        try:
            replay(bad)
        except ValueError:
            scope_failures += 1
        else:
            raise AssertionError('nonzero shared trace was silently dropped')

        selected = max(projected, key=len)
        chosen_patterns = patterns if d < 4 else (patterns[0], patterns[-1])
        labels = list(range(cursor+10, cursor+d+11))
        for pattern in chosen_patterns:
            outer = box([(s*labels[0], s*labels[i+1]) for i, s in enumerate(pattern)])
            compound = interleaved_product(outer, selected)
            image = signature(compound, 2*d)
            native = tuple(pattern[i//2] if i % 2 == 0 else 0 for i in range(2*d))
            demand({fixed: value for (word, fixed), value in image.items() if word == native} == selected,
                   'interleaved compound native image')
            for word, fixed in image:
                size = sum(bool(x) for x in word)
                demand(size != 1 and (size < d or word == native), 'interleaved compound protected spill')
            signatures += 1
        reports.append({'d': d, 'raw_products': len(raw), 'independent_trace_kernel_rank': len(basis),
                        'markers': len(markers), 'largest_projected_support': len(selected)})

    # Complete shared-trace signatures with noncontiguous complementary blocks.
    shared = 0
    for d in (2, 3, 4):
        patterns = [(1,)+s for s in product((-1, 1), repeat=d-1)]
        pairs = list(product(patterns, repeat=2))
        if d == 4:
            pairs = [pairs[i] for i in (0, 7, 19, 63)]
        for sigma, tau in pairs:
            left = box([(s*10, s*(11+i)) for i, s in enumerate(sigma)])
            right = box([(s*30, s*(31+i)) for i, s in enumerate(tau)])
            image = signature(interleaved_product(left, right), 2*d)
            word_left = tuple(sigma[i//2] if i % 2 == 0 else 0 for i in range(2*d))
            word_right = tuple(tau[i//2] if i % 2 else 0 for i in range(2*d))
            demand({fixed: value for (word, fixed), value in image.items() if word == word_left} == right,
                   'shared left output')
            demand({fixed: value for (word, fixed), value in image.items() if word == word_right} == left,
                   'shared right output')
            for word, fixed in image:
                size = sum(bool(x) for x in word)
                demand(size != 1 and (size < d or word in (word_left, word_right)),
                       'shared protected spill')
            shared += 1
    # Zero body traces are deliberately insufficient for the full inner kernel.
    inner = box([(1, 2), (1, 3), (4, 5)])
    margins_zero(inner, 3)
    demand(all(body(inner, (1,)+s) == 0 for s in product((-1, 1), repeat=2)), 'scope example body')
    demand(any(sum(bool(x) for x in word) == 2 for word, fixed in signature(inner, 3)),
           'missing smaller-contraction obstruction')
    outer = box([(10, 11), (10, 12), (10, 13)])
    lifted = signature(interleaved_product(outer, inner), 6)
    demand(any(word == (0, 1, 0, 1, 0, 0) for word, fixed in lifted),
           'the omitted complementary pair spill disappeared')

    splits = 0
    for n, g, coefficient in product((3, 5, 7), (2, 12, 30), range(-101, 102)):
        q, remainder = divmod(coefficient, n)
        parts = [g*(q+int(i < remainder)) for i in range(n)]
        total = g*coefficient
        error_bound = (abs(total)+n-1)//n
        demand(sum(parts) == total and max(map(abs, parts)) <= error_bound+g, 'shared scalar split')
        splits += 1
    depths = {}
    for k in range(2, 21):
        depth = 3*k-k//2-4 if k % 2 or k == 2 else 5*k//2-2
        expected_levels = (2*k-3)+(k-k//2)+(2 if k % 2 == 0 and k >= 4 else 0)
        demand(depth+1 == expected_levels, 'half depth')
        step = Fraction(3, 20*(depth+1))
        end = Fraction(3, 5)+depth*step
        demand(step > 0 and end < Fraction(3, 4), 'finite depth ladder')
        depths[k] = depth
    return {'half_revision': HALF_REVISION, 'projection_reconstruction': reports,
            'residue_cases': residue_cases, 'nonzero_trace_rejections': scope_failures,
            'interleaved_compound_signatures': signatures, 'shared_signatures': shared,
            'exact_signed_scalar_splits': splits, 'depths': depths,
            'smaller_contraction_obstruction': True}


def routed_cut_control():
    # Finite graph rerouting checks cut monotonicity and degree accounting.
    # This cycle-plus-chords graph is not asserted to have expansion eight.
    size = 10
    supports = [{i, (i+1) % size} for i in range(size)]
    original = [(i, (i+1) % size) for i in range(size)]
    original += [(i, (i+3) % size) for i in range(size)]
    routed = []
    use = Counter()
    for u, v in original:
        if supports[u].isdisjoint(supports[v]):
            routed.append((u, v))
        else:
            options = [w for w in range(size) if w not in (u, v)
                       and supports[w].isdisjoint(supports[u])
                       and supports[w].isdisjoint(supports[v])]
            w = min(options, key=lambda x: (use[x], x)); use[w] += 1
            routed.extend(((u, w), (w, v)))
    for u, v in routed:
        demand(supports[u].isdisjoint(supports[v]), 'unrepaired support edge')
    original_degree, degree = Counter(), Counter()
    for u, v in original: original_degree.update((u, v))
    for u, v in routed: degree.update((u, v))
    demand(all(degree[v] <= original_degree[v]+2*use[v] for v in range(size)), 'routed degree accounting')
    for mask in range(1 << size):
        cut = lambda edge: bool(mask & (1 << edge[0])) != bool(mask & (1 << edge[1]))
        demand(sum(map(cut, routed)) >= sum(map(cut, original)), 'rerouting shrank a cut')
    return {'vertices': size, 'cuts_checked': 1 << size, 'original_edges': len(original),
            'routed_edges': len(routed), 'max_middle_use': max(use.values()),
            'max_degree': max(degree.values())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--half-source', type=Path)
    args = parser.parse_args()
    bind(args.source)
    geometry = []
    for k, n in ((2, 3), (3, 3), (4, 3), (5, 3), (6, 3), (2, 5), (3, 5)):
        lines = line_inventory(k, n)
        demand(len(lines) == ((n+2)**k-n**k)//2, 'full line inventory')
        geometry.append((k, n, len(lines)))
    fixtures = []
    rejected = 0
    for k in (5, 6):
        data = json.loads((args.source/PREFIX/f'inputs/hyperk-controller-k{k}-stage.json').read_text())
        fixtures.append((k, *partial_prime_stage(data)))
        bad = []
        z = deepcopy(data); z['kind'] = 'prime-array-exact-pool'; bad.append(z)
        z = deepcopy(data); z['assignments'][0][1] = 9; bad.append(z)
        z = deepcopy(data); z['switch_pairs'].append(z['switch_pairs'][0]); bad.append(z)
        z = deepcopy(data); z['switch_pairs'].pop(); bad.append(z)
        z = deepcopy(data); z['gap'] += 2; bad.append(z)
        z = deepcopy(data); z['factors'][0].reverse(); bad.append(z)
        z = deepcopy(data); z['assignments'][1][1] = z['assignments'][0][1]; bad.append(z)
        for corruption in bad:
            try:
                partial_prime_stage(corruption)
            except (ValueError, TypeError, KeyError):
                rejected += 1
            else:
                raise AssertionError('corruption accepted')
    report = {'revision': REVISION, 'source_hashes': len(BINDINGS),
                      'geometry': geometry, 'partial_prime_stages': fixtures,
                      'local_load_cases': local_load_controls(),
                      'independent_majority_signatures': arbitrary_orientation_controls(),
                      'exact_obstructions': obstructions(), 'corruptions_rejected': rejected,
                      'scope': 'finite independent controls, not asymptotic packing or an arrangement'}
    if args.half_source:
        bind(args.half_source)
        bind(args.half_source, HALF_BINDINGS)
        report['half'] = half_controls()
        report['marker_rerouting'] = routed_cut_control()
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
