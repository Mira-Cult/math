#!/usr/bin/env python3
"""Exact integer incidence and constructive lifts for full signed 4-cubes.

This is numeric incidence code, not a permutation or prime-arrangement
constructor.  Coordinates are centered.  A line key is (varying, signs,
fixed), with increasing varying coordinates and first sign +1.  The
independent verifier regenerates line sets without this representation.

The eventual lift is the explicit n>=17 proof in hyper4_incidence.md.
The reduced Smith diagnostics use the integral axis-kernel basis and
integer coordinates on zero-margin/zero-total extra families.  Their
operation logs are independently replayable finite certificates.
"""

from __future__ import annotations

import argparse
from itertools import combinations, product
import json
from pathlib import Path


DIMENSION = 4
COORDINATES = tuple(range(DIMENSION))


def levels(n):
    if type(n) is not int or n < 3 or n % 2 != 1:
        raise ValueError("An odd integer n>=3 is required")
    return tuple(range(-(n // 2), n // 2 + 1))


def families(minimum=1, maximum=4):
    for size in range(minimum, maximum + 1):
        for varying in combinations(COORDINATES, size):
            for tail in product((1, -1), repeat=size - 1):
                yield varying, (1,) + tail


def complement(varying):
    return tuple(i for i in COORDINATES if i not in varying)


def line_keys(n):
    values = levels(n)
    for varying, signs in families():
        for fixed in product(values, repeat=4 - len(varying)):
            yield varying, signs, fixed


def line_cells(n, key):
    varying, signs, fixed = key
    result = []
    for t in levels(n):
        point = [None] * 4
        for i, sign in zip(varying, signs):
            point[i] = sign * t
        for i, value in zip(complement(varying), fixed):
            point[i] = value
        result.append(tuple(point))
    return tuple(result)


def line_sets(n):
    return {key: frozenset(line_cells(n, key)) for key in line_keys(n)}


def point_lines(point):
    for varying, signs in families():
        t = point[varying[0]]
        if all(point[i] == sign * t for i, sign in zip(varying, signs)):
            yield varying, signs, tuple(point[i] for i in complement(varying))


def line_sums(n, array):
    result = dict.fromkeys(line_keys(n), 0)
    for point, value in array.items():
        if value:
            for key in point_lines(point):
                result[key] += value
    return result


def cuboid(pairs):
    if len(pairs) != 4 or any(len(pair) != 2 or pair[0] == pair[1] for pair in pairs):
        raise ValueError("Four pairs of distinct coordinate endpoints are required")
    return {tuple(pairs[i][bit] for i, bit in enumerate(bits)):
            (-1) ** sum(bits) for bits in product((0, 1), repeat=4)}


def add_sparse(destination, source, coefficient=1):
    for point, value in source.items():
        destination[point] = destination.get(point, 0) + coefficient * value
        if not destination[point]:
            del destination[point]


def free_orbits(n, forbidden, count):
    forbidden = {abs(x) for x in forbidden if x}
    answer = [a for a in range(1, n // 2 + 1) if a not in forbidden][:count]
    if len(answer) != count:
        raise ValueError("Insufficient noncentral reflection orbits")
    return answer


def selector(n, sign, forbidden=()):
    """A generic rectangle with signed trace vector (1,0) or (0,1)."""
    if sign not in (1, -1):
        raise ValueError("A relative sign must be +1 or -1")
    a, b, c = free_orbits(n, forbidden, 3)
    return (a, b), (sign * a, sign * c)


def body_cuboid(n, signs):
    a, *auxiliary = free_orbits(n, (), 5)
    return tuple((sign * a, sign * b) for sign, b in zip(signs, auxiliary))


def triple_cuboid(n, varying, signs, u, v):
    if len(varying) != 3 or u == v:
        raise ValueError("A triple family and distinct transfer endpoints are required")
    a, *auxiliary = free_orbits(n, (u, v), 4)
    pairs = [None] * 4
    for i, sign, b in zip(varying, signs, auxiliary):
        pairs[i] = sign * a, sign * b
    pairs[complement(varying)[0]] = u, v
    return tuple(pairs)


def trace_cuboid(n, first, first_sign, second_sign):
    second = complement(first)
    first_pairs = selector(n, first_sign)
    forbidden = [x for pair in first_pairs for x in pair]
    second_pairs = selector(n, second_sign, forbidden)
    pairs = [None] * 4
    for i, pair in zip(first, first_pairs):
        pairs[i] = pair
    for i, pair in zip(second, second_pairs):
        pairs[i] = pair
    return tuple(pairs)


def rectangle_trace(pairs, sign):
    return sum((-1) ** (i + j) for i, x in enumerate(pairs[0])
               for j, y in enumerate(pairs[1]) if y == sign * x)


def rectangle_cells(pairs):
    return {(x, y): (-1)**(i+j) for i, x in enumerate(pairs[0])
            for j, y in enumerate(pairs[1])}


def template_cells(components):
    """Require disjoint +/-1 rectangles, as the compound physical form needs."""
    result = {}
    for coefficient, rectangle in components:
        if coefficient not in (-1, 1):
            raise ValueError("Template components must have coefficient +1 or -1")
        cells = rectangle_cells(rectangle)
        if len(cells) != 4 or result.keys() & cells.keys():
            raise ValueError("Template rectangles have repeated endpoints or hidden support collisions")
        result.update({cell: coefficient*value for cell, value in cells.items()})
    return result


def marker_projection_plan(n, edges):
    """Finite producer for MP4/MR4 patterns; edge copies remain labeled.

    Greedy least-used orbits are a convenient refinement of the proof's
    cap argument.  A finite allocation failure is reported, not called a
    theorem counterexample.  The theorem concerns sufficiently large n.
    """
    values = set(levels(n))
    edges = tuple(tuple(edge) for edge in edges)
    if any(len(edge) != 2 or edge[0] == edge[1] or not set(edge) <= values for edge in edges):
        raise ValueError("Edges must be labeled loopless pairs on the centered coordinate set")
    orbit_use = {a: 0 for a in range(1, n//2+1)}
    markers, templates = [], []
    for e, first in enumerate(edges):
        for f, second in enumerate(edges):
            rectangle = first, second
            components = [(1, rectangle)]
            forbidden = {abs(x) for pair in rectangle for x in pair if x}
            for sign in (1, -1):
                trace = rectangle_trace(rectangle, sign)
                for _ in range(abs(trace)):
                    available = sorted((count, a) for a, count in orbit_use.items() if a not in forbidden)
                    if len(available) < 3:
                        raise ValueError("Finite marker allocation exhausted its allowed orbits")
                    a, b, c = [item[1] for item in available[:3]]
                    local = ((a, b), (sign*a, sign*c))
                    contribution_sign = 1 if trace > 0 else -1
                    components.append((-contribution_sign, local))
                    markers.append({"sign": sign, "source": (e, f), "coefficient": contribution_sign,
                                    "rectangle": local})
                    for label in (a, b, c):
                        orbit_use[label] += 1
                        forbidden.add(label)
            template_cells(components)
            templates.append({"source": (e, f), "components": components})
    return {"n": n, "edges": edges, "markers": markers, "templates": templates,
            "max_orbit_use": max(orbit_use.values(), default=0)}


def routed_marker_paths(plan):
    """MR4 bounded-degree paths whose endpoint rectangles are disjoint."""
    markers = plan["markers"]
    supports = [set(rectangle_cells(marker["rectangle"])) for marker in markers]
    result = {}
    for sign in (1, -1):
        indices = [i for i, marker in enumerate(markers) if marker["sign"] == sign]
        use = dict.fromkeys(indices, 0)
        paths = []
        for position, (u, v) in enumerate(zip(indices, indices[1:])):
            if supports[u].isdisjoint(supports[v]):
                paths.append((u, v, position))
                continue
            available = [w for w in indices if use[w] < 4 and w not in (u, v)
                         and supports[w].isdisjoint(supports[u] | supports[v])]
            if not available:
                raise ValueError("Finite disjoint-marker path repair found no legal middle vertex")
            w = min(available, key=lambda j: (use[j], j))
            use[w] += 1
            paths.extend(((u, w, position), (w, v, position)))
        result[sign] = {"vertices": indices, "edges": paths}
    return result


def check_marker_paths(plan, paths):
    markers = plan["markers"]
    supports = [set(rectangle_cells(marker["rectangle"])) for marker in markers]
    if set(paths) != {1, -1}:
        raise ValueError("Both marker signs require a fixed routed path")
    for sign in (1, -1):
        indices = [i for i, marker in enumerate(markers) if marker["sign"] == sign]
        if paths[sign]["vertices"] != indices:
            raise ValueError("Marker path has a missing, duplicated or reordered vertex")
        routed = [[] for _ in indices[:-1]]
        degrees = dict.fromkeys(indices, 0)
        for u, v, position in paths[sign]["edges"]:
            if (u not in degrees or v not in degrees or not 0 <= position < len(routed)
                    or not supports[u].isdisjoint(supports[v])):
                raise ValueError("Marker path contains a support collision or an invalid vertex")
            routed[position].append((u, v))
            degrees[u] += 1
            degrees[v] += 1
        if max(degrees.values(), default=0) > 10:
            raise ValueError("The whole marker path exceeds the degree-ten load contract")
        for j, edges in enumerate(routed):
            if not ((len(edges) == 1 and edges[0] == (indices[j], indices[j+1]))
                    or (len(edges) == 2 and edges[0][0] == indices[j]
                        and edges[0][1] == edges[1][0] and edges[1][1] == indices[j+1])):
                raise ValueError("Routed edges do not realize the original marker path")


def tree_modular_flow(n, edges, demands, modulus):
    """Integral-tree flow over Z/hZ, without any division in that ring."""
    if type(modulus) is not int or modulus < 1:
        raise ValueError("Positive integer modulus required")
    vertices = levels(n)
    if set(demands) != set(vertices) or sum(demands.values()) % modulus:
        raise ValueError("Residue demands must have zero total on every vertex")
    adjacency = {v: [] for v in vertices}
    for index, (u, v) in enumerate(edges):
        adjacency[u].append((v, index))
        adjacency[v].append((u, index))
    root = vertices[0]
    parent = {root: None}
    order = [root]
    for u in order:
        for v, edge in adjacency[u]:
            if v not in parent:
                parent[v] = u, edge
                order.append(v)
    if len(order) != n:
        raise ValueError("The supplied graph is disconnected")
    residual = {v: demands[v] % modulus for v in vertices}
    flow = [0]*len(edges)
    for v in reversed(order[1:]):
        u, edge = parent[v]
        flow[edge] = (residual[v] if edges[edge][0] == v else -residual[v]) % modulus
        residual[u] = (residual[u]+residual[v]) % modulus
    return flow


def residue_pair_decomposition(plan, matrix, modulus, paths=None):
    """MR4 coefficients on preplanned compound templates and marker paths."""
    n, edges, markers = plan["n"], plan["edges"], plan["markers"]
    if type(modulus) is not int or modulus < 1:
        raise ValueError("Positive integer modulus required")
    values = levels(n)
    if any(sum(matrix.get((x, y), 0) for y in values) % modulus for x in values):
        raise ValueError("Nonzero row residue")
    if any(sum(matrix.get((x, y), 0) for x in values) % modulus for y in values):
        raise ValueError("Nonzero column residue")
    if any(sum(matrix.get((x, sign*x), 0) for x in values) % modulus for sign in (1, -1)):
        raise ValueError("Nonzero signed-trace residue")
    first = [tree_modular_flow(n, edges, {x: matrix.get((x, y), 0) for x in values}, modulus)
             for y in values]
    coefficients = [tree_modular_flow(n, edges, {y: first[j][e] for j, y in enumerate(values)}, modulus)
                    for e in range(len(edges))]
    mu = [(marker["coefficient"]*coefficients[marker["source"][0]][marker["source"][1]]) % modulus
          for marker in markers]
    paths = routed_marker_paths(plan) if paths is None else paths
    check_marker_paths(plan, paths)
    marker_flows = []
    for sign in (1, -1):
        path = paths[sign]
        indices = path["vertices"]
        if sum(mu[i] for i in indices) % modulus:
            raise AssertionError("Projected marker residues do not have zero total")
        prefixes, running = [], 0
        for index in indices[:-1]:
            running = (running+mu[index]) % modulus
            prefixes.append(running)
        for u, v, position in path["edges"]:
            marker_flows.append((prefixes[position], u, v))
    return {"coefficients": coefficients, "marker_flows": marker_flows}


def pure_pair_terms(n, varying, sign, u, v):
    """Return a short integer sum with one trace-free native pair image.

    Its native image is R_uv-beta_+(R_uv)Q_+-beta_-(R_uv)Q_-.
    Supports need not be disjoint.  This is the saturation proof, not the
    separate bounded marker-projection architecture used physically.
    """
    if not u or not v or len(varying) != 2:
        raise ValueError("Noncentral anchored coordinates and a pair family are required")
    remaining = complement(varying)
    rectangle = ((u, 0), (v, 0))
    plus, minus = selector(n, 1), selector(n, -1)
    forbidden = [x for pairs in (rectangle, plus, minus) for pair in pairs for x in pair]
    native = selector(n, sign, forbidden)
    result = []
    for weight, local in ((1, rectangle), (-rectangle_trace(rectangle, 1), plus),
                          (-rectangle_trace(rectangle, -1), minus)):
        if not weight:
            continue
        pairs = [None] * 4
        for i, pair in zip(varying, native):
            pairs[i] = pair
        for i, pair in zip(remaining, local):
            pairs[i] = pair
        result.append((weight, tuple(pairs)))
    return result


def matrix_trace(target, varying, signs, sign, n):
    return sum(target[(varying, signs, (t, sign * t))] for t in levels(n))


def compatibility_errors(n, target, total=None):
    """All partition identities, without pretending the list is independent."""
    values = levels(n)
    required = set(line_keys(n))
    if set(target) != required or any(type(value) is not int for value in target.values()):
        return ["Wrong line-key set or a noninteger target"]
    errors = []

    def axis(i, point):
        return target[((i,), (1,), tuple(point[j] for j in COORDINATES if j != i))]

    for i, j in combinations(COORDINATES, 2):
        rest = tuple(k for k in COORDINATES if k not in (i, j))
        for fixed in product(values, repeat=2):
            point = dict(zip(rest, fixed))
            left = sum(axis(i, {**point, j: t}) for t in values)
            right = sum(axis(j, {**point, i: t}) for t in values)
            if left != right:
                errors.append(("axis", i, j, fixed, left, right))

    for varying, signs in families(2, 2):
        rest = complement(varying)
        for summed_position, summed in enumerate(rest):
            fixed_coordinate = rest[1 - summed_position]
            for fixed in values:
                left = sum(target[(varying, signs, (t, fixed) if summed_position == 0 else (fixed, t))]
                           for t in values)
                right = 0
                for t in values:
                    point = {i: sign * t for i, sign in zip(varying, signs)}
                    point[fixed_coordinate] = fixed
                    right += axis(summed, point)
                if left != right:
                    errors.append(("pair-margin", varying, signs, summed, fixed, left, right))

    for varying, signs in families(3, 3):
        remaining = complement(varying)[0]
        left = sum(target[(varying, signs, (t,))] for t in values)
        right = sum(axis(remaining, {i: sign * t for i, sign in zip(varying, signs)})
                    for t in values)
        if left != right:
            errors.append(("triple-total", varying, signs, left, right))

    for first in ((0, 1), (0, 2), (0, 3)):
        second = complement(first)
        for sigma, tau in product((1, -1), repeat=2):
            left = matrix_trace(target, first, (1, sigma), tau, n)
            right = matrix_trace(target, second, (1, tau), sigma, n)
            if left != right:
                errors.append(("pair-pair", first, sigma, tau, left, right))
    if total is not None:
        observed = sum(value for (varying, _, _), value in target.items() if varying == (0,))
        if observed != total:
            errors.append(("total", observed, total))
    return errors


def integer_lift(n, target, residue=None, modulus=None, return_log=False):
    """Construct a signed-integer lift; no positivity or prescribed pool promise."""
    values = levels(n)
    if n < 17:
        raise ValueError("The uniform constructive lift requires n>=17")
    errors = compatibility_errors(n, target)
    if errors:
        raise ValueError(f"Incompatible targets: {errors[0]}")
    if (residue is None) != (modulus is None):
        raise ValueError("Specify both residue and modulus or neither")
    if modulus is not None:
        if type(modulus) is not int or modulus < 1 or type(residue) is not int:
            raise ValueError("Invalid entry congruence")
        if any((value - n * residue) % modulus for value in target.values()):
            raise ValueError("Line congruence does not permit the requested entry congruence")
        reduced = {key: (value - n * residue) // modulus for key, value in target.items()}
        lift = integer_lift(n, reduced)
        array = {point: residue + modulus * lift.get(point, 0) for point in product(values, repeat=4)}
        return {point: value for point, value in array.items() if value}

    array = {}
    for i in COORDINATES:
        current = line_sums(n, array)
        for fixed in product(values, repeat=3):
            key = (i,), (1,), fixed
            change = target[key] - current[key]
            if change:
                point = list(fixed)
                point.insert(i, 0)
                point = tuple(point)
                array[point] = array.get(point, 0) + change
                if not array[point]:
                    del array[point]
    current = line_sums(n, array)
    residual = {key: value - current[key] for key, value in target.items()}
    log = []

    def apply(coefficient, pairs, stage):
        if not coefficient:
            return
        change = cuboid(pairs)
        add_sparse(array, change, coefficient)
        for point, value in change.items():
            for key in point_lines(point):
                residual[key] -= coefficient * value
        log.append((stage, coefficient, pairs))

    for varying, signs in families(4, 4):
        apply(residual[(varying, signs, ())], body_cuboid(n, signs), "body")
    for varying, signs in families(3, 3):
        for u in values:
            if u:
                apply(residual[(varying, signs, (u,))],
                      triple_cuboid(n, varying, signs, u, 0), "triple")
    for first in ((0, 1), (0, 2), (0, 3)):
        for sigma, tau in product((1, -1), repeat=2):
            change = matrix_trace(residual, first, (1, sigma), tau, n)
            apply(change, trace_cuboid(n, first, sigma, tau), "trace")
    for varying, signs in families(2, 2):
        coefficients = {(u, v): residual[(varying, signs, (u, v))]
                        for u in values if u for v in values if v}
        for (u, v), coefficient in coefficients.items():
            if coefficient:
                for weight, pairs in pure_pair_terms(n, varying, signs[1], u, v):
                    apply(coefficient * weight, pairs, "pure-pair")
    if any(residual.values()):
        raise AssertionError("Constructive lift left a nonzero line residual")
    return (array, log) if return_log else array


def reduced_axis_kernel_matrix(n):
    """Integer-coordinate image on the anchored integral axis-kernel basis."""
    nonzero = tuple(x for x in levels(n) if x)
    rows = [(varying, signs, fixed) for varying, signs in families(2, 4)
            for fixed in product(nonzero, repeat=4 - len(varying))]
    columns = list(product(nonzero, repeat=4))
    row_index = {key: i for i, key in enumerate(rows)}
    matrix = [[0] * len(columns) for _ in rows]
    for column, point in enumerate(columns):
        for varying, signs in families(2, 4):
            aligned = all(point[i] == sign * point[varying[0]]
                          for i, sign in zip(varying, signs))
            coefficient = (-1) ** len(varying) + int(aligned)
            if coefficient:
                fixed = tuple(point[i] for i in complement(varying))
                matrix[row_index[(varying, signs, fixed)]][column] = coefficient
    return rows, columns, matrix


def small_smith_certificate(n):
    if n not in (3, 5):
        raise ValueError("Retained finite Smith diagnostics are restricted to n=3,5")
    rows, columns, matrix = reduced_axis_kernel_matrix(n)
    if n == 3:
        diagnostic = {"method": "elementary-operations", "smith": smallest_pivot_smith(matrix)}
    else:
        diagnostic = block_smith_certificate(matrix)
    certificate = {
        "kind": "signed-hyper4-reduced-integer-incidence",
        "n": n,
        "coordinate_order": "centered increasing; family size, coordinates, signs + before -, fixed lexicographic",
        "basis": "tensor product (e_i-e_0) for all four noncentral indices",
        "rows": len(rows), "columns": len(columns),
        "full_line_count": 4*n**3 + 12*n**2 + 16*n + 8,
        "axis_rank": n**4 - (n - 1)**4,
        **diagnostic,
        "scope": "Exact integer incidence only; neither a target-prime nor a prescribed-pool certificate.",
    }
    certificate.update(export_lattice_bases(certificate))
    return certificate


def pullback_operations(vector, operations, kind):
    """Multiply by the logged domain transform or pull back a codomain row."""
    result = list(vector)
    for operation in reversed(operations):
        tag, *arguments = operation
        if tag[0] != kind:
            continue
        if tag[1] == "s":
            i, j = arguments
            result[i], result[j] = result[j], result[i]
        elif tag[1] == "a":
            destination, source, coefficient = arguments
            result[source] += coefficient*result[destination]
        else:
            result[arguments[0]] *= -1
    return result


def export_lattice_bases(certificate):
    rows, columns = certificate["rows"], certificate["columns"]

    def unit(length, index):
        return [int(i == index) for i in range(length)]

    def sparse(vector):
        return [[i, value] for i, value in enumerate(vector) if value]

    if certificate["method"] == "elementary-operations":
        smith = certificate["smith"]
        rank = len(smith["diagonal"])
        kernels = [pullback_operations(unit(columns, j), smith["operations"], "c")
                   for j in range(rank, columns)]
        dependencies = [pullback_operations(unit(rows, i), smith["operations"], "r")
                        for i in range(rank, rows)]
        congruences = [[factor, sparse(pullback_operations(unit(rows, i), smith["operations"], "r"))]
                       for i, factor in enumerate(smith["diagonal"]) if factor != 1]
    else:
        prefix, rank = certificate["prefix"], certificate["tail_rank"]
        left, right = certificate["left"], certificate["right"]
        pre = certificate["precondition_operations"]
        kernels = [pullback_operations([0]*prefix+[row[j] for row in right], pre, "c")
                   for j in range(rank, len(right))]
        dependencies = [pullback_operations([0]*prefix+row, pre, "r") for row in left[rank:]]
        congruences = []
        for i, factor in enumerate(certificate["tail_smith"]["diagonal"]):
            if factor == 1:
                continue
            coefficients = pullback_operations(unit(rank, i), certificate["tail_smith"]["operations"], "r")
            row = [sum(coefficient*left[k][j] for k, coefficient in enumerate(coefficients))
                   for j in range(len(left))]
            congruences.append([factor, sparse(pullback_operations([0]*prefix+row, pre, "r"))])
    return {"kernel_basis": [sparse(vector) for vector in kernels],
            "dependency_basis": [sparse(vector) for vector in dependencies],
            "image_divisibility": congruences}


def block_smith_certificate(matrix):
    """Producer-only FLINT acceleration; verification is standard-library only.

    All returned transforms have explicit integer inverses.  The checker
    verifies both inverse identities and the full transformed block, then
    replays a small Smith operation log.  No black-box rank is trusted.
    """
    import flint
    if flint.__version__ != "0.8.0":
        raise RuntimeError("The retained n=5 producer is pinned to python-flint 0.8.0")
    from flint import fmpz_mat
    from signed_kernel_certificate import unit_pivot_precondition
    reduced, operations = unit_pivot_precondition(matrix)
    prefix = 0
    while prefix < min(len(reduced), len(reduced[0])) and reduced[prefix][prefix] == 1:
        prefix += 1
    trailing = fmpz_mat([row[prefix:] for row in reduced[prefix:]])
    column_hnf, right_transpose = trailing.transpose().hnf(transform=True)
    rank = sum(any(value for value in row) for row in column_hnf.tolist())
    right = right_transpose.transpose()
    image = column_hnf.transpose()
    image = fmpz_mat([[image[i, j] for j in range(rank)] for i in range(image.nrows())])
    block, left = image.hnf(transform=True)
    square = [[int(block[i, j]) for j in range(rank)] for i in range(rank)]

    def integers(array):
        return [[int(value) for value in row] for row in array.tolist()]

    return {
        "method": "unit-preconditioned-unimodular-block",
        "producer_dependency": "python-flint==0.8.0; producer only",
        "prefix": prefix,
        "precondition_operations": operations,
        "tail_rank": rank,
        "left": integers(left), "left_inverse": integers(left.inv(integer=True)),
        "right": integers(right), "right_inverse": integers(right.inv(integer=True)),
        "square": square,
        "tail_smith": smallest_pivot_smith(square),
    }


def smallest_pivot_smith(matrix):
    """Smith producer with smallest pivots and an explicit unimodular log.

    The unchanged three-dimensional first-nonzero reducer can develop huge
    intermediate coefficients on this different matrix.  Pivot selection
    is an optimization only: an independent replay validates every step.
    Among equally small entries, minimize the same fill proxy as PR79.
    """
    a = [row[:] for row in matrix]
    rows, columns = len(a), len(a[0])
    operations = []

    def rs(i, j):
        if i != j:
            a[i], a[j] = a[j], a[i]
            operations.append(["rs", i, j])

    def cs(i, j):
        if i != j:
            for row in a:
                row[i], row[j] = row[j], row[i]
            operations.append(["cs", i, j])

    def ra(i, j, coefficient):
        if coefficient:
            a[i] = [x + coefficient*y for x, y in zip(a[i], a[j])]
            operations.append(["ra", i, j, coefficient])

    def ca(i, j, coefficient):
        if coefficient:
            for row in a:
                row[i] += coefficient*row[j]
            operations.append(["ca", i, j, coefficient])

    rank = 0
    while rank < min(rows, columns):
        minimum = min((abs(a[i][j]) for i in range(rank, rows)
                       for j in range(rank, columns) if a[i][j]), default=None)
        if minimum is None:
            break
        row_counts = [sum(value != 0 for value in row[rank:]) for row in a]
        column_counts = [sum(a[i][j] != 0 for i in range(rank, rows)) for j in range(columns)]
        _, i, j = min(((row_counts[i]-1)*(column_counts[j]-1), i, j)
                      for i in range(rank, rows) for j in range(rank, columns)
                      if abs(a[i][j]) == minimum)
        rs(rank, i)
        cs(rank, j)
        while True:
            remaining = [(abs(a[i][rank]), i) for i in range(rank+1, rows) if a[i][rank]]
            if remaining:
                _, i = min(remaining)
                ra(i, rank, -(a[i][rank] // a[rank][rank]))
                if a[i][rank]:
                    rs(i, rank)
                continue
            remaining = [(abs(a[rank][j]), j) for j in range(rank+1, columns) if a[rank][j]]
            if remaining:
                _, j = min(remaining)
                ca(j, rank, -(a[rank][j] // a[rank][rank]))
                if a[rank][j]:
                    cs(j, rank)
                continue
            nondivisible = min(((abs(a[i][j]), i, j) for i in range(rank+1, rows)
                                for j in range(rank+1, columns) if a[i][j] % a[rank][rank]),
                               default=None)
            if nondivisible is None:
                break
            _, i, _ = nondivisible
            ra(rank, i, 1)
        if a[rank][rank] < 0:
            a[rank] = [-value for value in a[rank]]
            operations.append(["rn", rank])
        rank += 1
    return {"shape": [rows, columns], "diagonal": [a[i][i] for i in range(rank)],
            "operations": operations}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smith", type=int, choices=(3, 5))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.smith is None:
        parser.error("Choose --smith 3 or --smith 5")
    certificate = small_smith_certificate(args.smith)
    encoded = json.dumps(certificate, sort_keys=True, separators=(",", ":")) + "\n"
    if args.output:
        args.output.write_text(encoded)
        factors = (certificate["smith"]["diagonal"] if certificate["method"] == "elementary-operations"
                   else [1]*certificate["prefix"]+certificate["tail_smith"]["diagonal"])
        print(json.dumps({"n": args.smith, "rank": certificate["axis_rank"] + len(factors),
                          "nonunit_factors": [value for value in factors if value != 1],
                          "method": certificate["method"]}))
    else:
        print(encoded, end="")


if __name__ == "__main__":
    main()
