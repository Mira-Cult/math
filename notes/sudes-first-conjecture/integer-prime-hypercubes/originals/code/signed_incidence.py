"""Exact full signed-line incidence on odd cubes, with integer certificates.

Coordinates are 0,...,n-1 and reflection is t -> n-1-t.  The large-order
constructive routines require odd n >= 11.  They manipulate signed integer
arrays, not permutations of a prescribed pool.  No prime-supply assertion is
made here.  Only the Python standard library and the frozen incidence module
are used.
"""

from collections import deque
from fractions import Fraction
from itertools import combinations, product

from incidence import compatible_axes, flat_index, integer_axis_lift


def _int(value):
    rational = Fraction(value)
    if rational.denominator != 1:
        raise ValueError("integer required")
    return rational.numerator


def _order(n, minimum=3):
    n = _int(n)
    if n < minimum or n % 2 == 0:
        raise ValueError(f"odd order at least {minimum} required")
    return n


def reflected(value, sign, n):
    if sign not in (-1, 1):
        raise ValueError("sign must be +1 or -1")
    return value if sign == 1 else n - 1 - value


def face_families():
    return [(a, b, sign) for a, b in combinations(range(3), 2)
            for sign in (1, -1)]


def line_sets(n):
    """Keyed, deduplicated axis/face/body subsets, in a fixed canonical order."""
    n = _order(n)
    result = {}
    for axis in range(3):
        for fixed in product(range(n), repeat=2):
            edge = []
            for t in range(n):
                point = fixed[:axis] + (t,) + fixed[axis:]
                edge.append(flat_index(point, n))
            result[("axis", axis, fixed)] = frozenset(edge)
    for a, b, sign in face_families():
        free = 3 - a - b
        for level in range(n):
            edge = []
            for t in range(n):
                point = [0] * 3
                point[a], point[b], point[free] = t, reflected(t, sign, n), level
                edge.append(flat_index(point, n))
            result[("face", a, b, sign, level)] = frozenset(edge)
    for sy, sz in product((1, -1), repeat=2):
        result[("body", sy, sz)] = frozenset(
            flat_index((t, reflected(t, sy, n), reflected(t, sz, n)), n)
            for t in range(n)
        )
    assert len(set(result.values())) == len(result) == 3 * n * n + 6 * n + 4
    return result


def extra_keys(n):
    n = _order(n)
    return [
        ("face", a, b, sign, level)
        for a, b, sign in face_families() for level in range(n)
    ] + [("body", sy, sz) for sy, sz in product((1, -1), repeat=2)]


def line_sums(values, n):
    if len(values) != n ** 3:
        raise ValueError("wrong cube length")
    return {key: sum(values[i] for i in edge)
            for key, edge in line_sets(n).items()}


def compatible_targets(targets, n):
    """Check the rational equations (not sufficient at n=3 or n=5)."""
    n = _order(n)
    if set(targets) != set(line_sets(n)):
        return False
    axes = [[targets[("axis", axis, fixed)]
             for fixed in product(range(n), repeat=2)] for axis in range(3)]
    if not compatible_axes(axes, n, 3):
        return False
    for a, b, sign in face_families():
        free = 3 - a - b
        face_total = sum(targets[("face", a, b, sign, level)] for level in range(n))
        axis_total = sum(targets[("axis", free, (t, reflected(t, sign, n)))]
                         for t in range(n))
        if face_total != axis_total:
            return False
    return True


def cuboid(pairs, n):
    """Sparse eight-corner tensor product of three oriented differences."""
    n = _int(n)
    if len(pairs) != 3 or any(len(pair) != 2 for pair in pairs):
        raise ValueError("three coordinate pairs required")
    pairs = tuple(tuple(_int(value) for value in pair) for pair in pairs)
    if any(u == v or not (0 <= u < n and 0 <= v < n) for u, v in pairs):
        raise ValueError("pairs must have distinct coordinates inside the cube")
    return {
        flat_index(tuple(pairs[axis][bit] for axis, bit in enumerate(bits)), n):
        (-1) ** sum(bits)
        for bits in product((0, 1), repeat=3)
    }


def sparse_line_sums(values, n, edges=None):
    edges = line_sets(n) if edges is None else edges
    return {key: sum(value for cell, value in values.items() if cell in edge)
            for key, edge in edges.items()}


def face_cuboid(n, a, b, sign, u, v):
    """Unit e_u-e_v transfer in one face family, all other lines unchanged."""
    n = _order(n, 11)
    a, b, sign, u, v = (_int(value) for value in (a, b, sign, u, v))
    if (a, b, sign) not in face_families() or u == v or not (0 <= u < n and 0 <= v < n):
        raise ValueError("invalid face transfer")
    center = n // 2
    forbidden = {abs(u - center), abs(v - center)}
    representatives = [center + k for k in range(1, center + 1) if k not in forbidden]
    t, x, y = representatives[:3]
    pairs = [None] * 3
    pairs[a] = (t, x)
    pairs[b] = (reflected(t, sign, n), reflected(y, sign, n))
    pairs[3 - a - b] = (u, v)
    return tuple(pairs)


def body_cuboid(n, sy, sz):
    """Unit body transfer, plus three explicit zero-total face transfers."""
    n = _order(n, 11)
    t, a, b, c = range(n // 2 + 1, n // 2 + 5)
    return ((t, a), (reflected(t, sy, n), reflected(b, sy, n)),
            (reflected(t, sz, n), reflected(c, sz, n)))


def pure_body_plan(n, sy, sz):
    """At most four cuboids with image a single unit body coordinate."""
    pairs = body_cuboid(n, sy, sz)
    plan = [(1, pairs)]
    image = sparse_line_sums(cuboid(pairs, n), n)
    for a, b, sign in face_families():
        positive = [u for u in range(n) if image[("face", a, b, sign, u)] == 1]
        negative = [u for u in range(n) if image[("face", a, b, sign, u)] == -1]
        if positive:
            assert len(positive) == len(negative) == 1
            plan.append((-1, face_cuboid(n, a, b, sign, positive[0], negative[0])))
    assert len(plan) == 4
    return plan


def apply_plan(n, plan):
    out = [0] * n ** 3
    for coefficient, pairs in plan:
        coefficient = _int(coefficient)
        for cell, value in cuboid(pairs, n).items():
            out[cell] += coefficient * value
    return out


def integer_edge_flow(demands, edges, capacity=None):
    """Integral divergence, positive at the first endpoint of each edge.

    With a supplied capacity C, return coefficients in [-C,C], or raise if
    infeasible.  The implementation uses integer augmenting paths.  It does
    not assume or certify an expansion estimate for the supplied graph.
    """
    demands = [_int(x) for x in demands]
    n = len(demands)
    if not n or sum(demands):
        raise ValueError("nonempty zero-total demand required")
    edges = [tuple(edge) for edge in edges]
    if any(len(edge) != 2 or edge[0] == edge[1] or
           not all(isinstance(v, int) and 0 <= v < n for v in edge) for edge in edges):
        raise ValueError("loopless graph on the demand coordinates required")
    supply = sum(max(0, x) for x in demands)
    capacity = supply if capacity is None else _int(capacity)
    if capacity < 0:
        raise ValueError("nonnegative edge capacity required")
    source, sink = n, n + 1
    adjacency = [[] for _ in range(n + 2)]

    def arc(u, v, bound):
        forward = [v, bound, len(adjacency[v])]
        backward = [u, 0, len(adjacency[u])]
        adjacency[u].append(forward)
        adjacency[v].append(backward)
        return forward

    handles = [(arc(u, v, capacity), arc(v, u, capacity)) for u, v in edges]
    for v, demand in enumerate(demands):
        if demand > 0:
            arc(source, v, demand)
        elif demand < 0:
            arc(v, sink, -demand)
    sent = 0
    while sent < supply:
        parent = [None] * (n + 2)
        parent[source] = (source, -1)
        queue = deque([source])
        while queue and parent[sink] is None:
            u = queue.popleft()
            for index, edge in enumerate(adjacency[u]):
                v, remaining, _ = edge
                if remaining > 0 and parent[v] is None:
                    parent[v] = (u, index)
                    queue.append(v)
        if parent[sink] is None:
            raise ValueError("integer edge capacity is infeasible")
        bound = supply - sent
        v = sink
        while v != source:
            u, index = parent[v]
            bound = min(bound, adjacency[u][index][1])
            v = u
        v = sink
        while v != source:
            u, index = parent[v]
            edge = adjacency[u][index]
            edge[1] -= bound
            adjacency[v][edge[2]][1] += bound
            v = u
        sent += bound
    coefficients = [backward[1] - forward[1] for forward, backward in handles]
    divergence = [0] * n
    for (u, v), value in zip(edges, coefficients):
        divergence[u] += value
        divergence[v] -= value
    assert divergence == demands and all(abs(x) <= capacity for x in coefficients)
    return coefficients


def extra_correction_plan(n, targets, edges=None, capacity=None):
    """Lift zero-total face vectors and four arbitrary body values by cuboids.

    Correct bodies first, then faces.  With no graph, use the path and exact
    prefix sums.  With a graph, use the supplied integer edge capacity.
    """
    n = _order(n, 11)
    if set(targets) != set(extra_keys(n)):
        raise ValueError("all extra signed-line targets required")
    targets = {key: _int(value) for key, value in targets.items()}
    if any(sum(targets[("face", a, b, sign, u)] for u in range(n))
           for a, b, sign in face_families()):
        raise ValueError("face-family totals must vanish")
    plan = [(targets[("body", sy, sz)], body_cuboid(n, sy, sz))
            for sy, sz in product((1, -1), repeat=2) if targets[("body", sy, sz)]]
    current = line_sums(apply_plan(n, plan), n)
    graph = [(u, u + 1) for u in range(n - 1)] if edges is None else list(edges)
    for a, b, sign in face_families():
        demand = [targets[("face", a, b, sign, u)] - current[("face", a, b, sign, u)]
                  for u in range(n)]
        if edges is None:
            running = 0
            coefficients = []
            for value in demand[:-1]:
                running += value
                coefficients.append(running)
        else:
            coefficients = integer_edge_flow(demand, graph, capacity)
        plan.extend((value, face_cuboid(n, a, b, sign, u, v))
                    for (u, v), value in zip(graph, coefficients) if value)
    return plan


def integer_full_lift(targets, n, entry_residue=None, entry_modulus=None):
    """Integral full-line lift for odd n>=11, optionally in one entry class.

    The optional congruence requires every line target == n*entry_residue
    modulo entry_modulus.  This is numeric lifting, with no positivity or
    exact-pool conclusion.
    """
    n = _order(n, 11)
    targets = {key: _int(value) for key, value in targets.items()}
    if not compatible_targets(targets, n):
        raise ValueError("incompatible signed-line targets")
    if entry_modulus is not None or entry_residue is not None:
        if entry_modulus is None or entry_residue is None:
            raise ValueError("both entry residue and modulus are required")
        modulus, residue = _int(entry_modulus), _int(entry_residue)
        if modulus < 1 or any((value - n * residue) % modulus for value in targets.values()):
            raise ValueError("line congruence is incompatible with the entry class")
        reduced = {key: (value - n * residue) // modulus for key, value in targets.items()}
        lift = integer_full_lift(reduced, n)
        return [residue + modulus * value for value in lift]
    axes = [[targets[("axis", axis, fixed)]
             for fixed in product(range(n), repeat=2)] for axis in range(3)]
    lift = integer_axis_lift(axes, n, 3)
    current = line_sums(lift, n)
    remaining = {key: targets[key] - current[key] for key in extra_keys(n)}
    correction = apply_plan(n, extra_correction_plan(n, remaining))
    out = [x + y for x, y in zip(lift, correction)]
    assert line_sums(out, n) == targets
    return out


def residue_cuboid_plan(n, demands, modulus):
    """Step-two plan for even extra-line demands modulo an even modulus.

    Faces must have zero total modulo modulus.  Each returned coefficient is
    in 0,...,modulus/2-1, counting cuboids of actual step 2 modulo modulus.
    The geometry may be varied between repetitions without changing its
    isolated face image.  Body geometries here are fixed reference choices.
    """
    n = _order(n, 11)
    modulus = _int(modulus)
    if modulus < 2 or modulus % 2:
        raise ValueError("positive even modulus at least two required")
    if set(demands) != set(extra_keys(n)):
        raise ValueError("all extra-line demands required")
    demands = {key: _int(value) for key, value in demands.items()}
    if any(value % 2 for value in demands.values()):
        raise ValueError("even demands required")
    if any(sum(demands[("face", a, b, sign, u)] for u in range(n)) % modulus
           for a, b, sign in face_families()):
        raise ValueError("face totals must vanish modulo the modulus")
    half = modulus // 2
    reduced = {key: (value // 2) % half for key, value in demands.items()}
    plan = [(reduced[("body", sy, sz)], body_cuboid(n, sy, sz))
            for sy, sz in product((1, -1), repeat=2) if reduced[("body", sy, sz)]]
    current = line_sums(apply_plan(n, plan), n)
    for a, b, sign in face_families():
        running = 0
        for u in range(n - 1):
            key = ("face", a, b, sign, u)
            running = (running + reduced[key] - current[key]) % half
            if running:
                plan.append((running, face_cuboid(n, a, b, sign, u, u + 1)))
    return plan


def axis_kernel_extra_matrix(n):
    """Integral axis-kernel basis mapped to independent face slots + bodies.

    Omit the center coordinate of each zero-total face family.  Columns are
    (e_i-e_center) tensor (e_j-e_center) tensor (e_k-e_center), with i,j,k
    noncentral.  No rational basis changes are used.
    """
    n = _order(n)
    center = n // 2
    other = [i for i in range(n) if i != center]
    keys = [key for key in extra_keys(n) if key[0] == "body" or key[-1] != center]
    edges = line_sets(n)
    matrix = [[] for _ in keys]
    for i, j, k in product(other, repeat=3):
        values = cuboid(((i, center), (j, center), (k, center)), n)
        for row, key in zip(matrix, keys):
            row.append(sum(value for cell, value in values.items() if cell in edges[key]))
    return keys, matrix


def smith_certificate(matrix):
    """Exact Smith reduction with an independently replayable operation log.

    Operations are row/column swaps, sign reversals, and integer additions
    of one different row/column to another.  Thus every operation is visibly
    unimodular.  This reference implementation is intended for finite tests.
    """
    a = [[_int(x) for x in row] for row in matrix]
    rows = len(a)
    cols = len(a[0]) if rows else 0
    if not rows or not cols or any(len(row) != cols for row in a):
        raise ValueError("nonempty rectangular integer matrix required")
    operations = []

    def row_swap(i, j):
        a[i], a[j] = a[j], a[i]
        operations.append(("rs", i, j))

    def col_swap(i, j):
        for row in a:
            row[i], row[j] = row[j], row[i]
        operations.append(("cs", i, j))

    def row_add(target, source, multiplier):
        a[target] = [x + multiplier * y for x, y in zip(a[target], a[source])]
        operations.append(("ra", target, source, multiplier))

    def col_add(target, source, multiplier):
        for row in a:
            row[target] += multiplier * row[source]
        operations.append(("ca", target, source, multiplier))

    rank = 0
    while rank < min(rows, cols):
        nonzero = next(((i, j) for i in range(rank, rows) for j in range(rank, cols)
                        if a[i][j]), None)
        if nonzero is None:
            break
        i, j = nonzero
        if i != rank:
            row_swap(i, rank)
        if j != rank:
            col_swap(j, rank)
        while True:
            i = next((i for i in range(rank + 1, rows) if a[i][rank]), None)
            if i is not None:
                quotient = a[i][rank] // a[rank][rank]
                if quotient:
                    row_add(i, rank, -quotient)
                if a[i][rank]:
                    row_swap(i, rank)
                continue
            j = next((j for j in range(rank + 1, cols) if a[rank][j]), None)
            if j is not None:
                quotient = a[rank][j] // a[rank][rank]
                if quotient:
                    col_add(j, rank, -quotient)
                if a[rank][j]:
                    col_swap(j, rank)
                continue
            nondivisible = next(((i, j) for i in range(rank + 1, rows)
                                 for j in range(rank + 1, cols)
                                 if a[i][j] % a[rank][rank]), None)
            if nondivisible is None:
                break
            row_add(rank, nondivisible[0], 1)
        if a[rank][rank] < 0:
            a[rank] = [-x for x in a[rank]]
            operations.append(("rn", rank))
        rank += 1
    return {"shape": (rows, cols), "diagonal": [a[i][i] for i in range(rank)],
            "operations": operations}


def verify_smith_certificate(matrix, certificate):
    """Replay elementary operations; reject invalid or non-Smith output."""
    a = [[_int(x) for x in row] for row in matrix]
    rows, cols = len(a), len(a[0]) if a else 0
    if not rows or not cols or any(len(row) != cols for row in a):
        raise ValueError("nonempty rectangular matrix required")
    if tuple(certificate["shape"]) != (rows, cols):
        return False
    for operation in certificate["operations"]:
        op, *args = operation
        if op in ("rs", "cs"):
            if len(args) != 2:
                return False
            i, j = args
            limit = rows if op == "rs" else cols
            if not all(isinstance(k, int) and 0 <= k < limit for k in (i, j)):
                return False
            if op == "rs":
                a[i], a[j] = a[j], a[i]
            else:
                for row in a:
                    row[i], row[j] = row[j], row[i]
        elif op in ("ra", "ca"):
            if len(args) != 3:
                return False
            target, source, multiplier = args
            limit = rows if op == "ra" else cols
            if (target == source or not all(isinstance(k, int) and 0 <= k < limit
                                           for k in (target, source)) or
                    not isinstance(multiplier, int)):
                return False
            if op == "ra":
                a[target] = [x + multiplier * y for x, y in zip(a[target], a[source])]
            else:
                for row in a:
                    row[target] += multiplier * row[source]
        elif op == "rn":
            if len(args) != 1 or not isinstance(args[0], int) or not 0 <= args[0] < rows:
                return False
            a[args[0]] = [-x for x in a[args[0]]]
        else:
            return False
    diagonal = certificate["diagonal"]
    if (len(diagonal) > min(rows, cols) or
            any(not isinstance(x, int) or x <= 0 for x in diagonal) or
            any(b % a for a, b in zip(diagonal, diagonal[1:]))):
        return False
    return all(a[i][j] == (diagonal[i] if i == j and i < len(diagonal) else 0)
               for i in range(rows) for j in range(cols))


def smith_image_membership(target, certificate):
    """Apply the certified left row transformation and test divisibility.

    The caller must first verify the certificate against its matrix.  Column
    operations change the domain basis and hence need not act on the target.
    """
    target = [_int(x) for x in target]
    if len(target) != certificate["shape"][0]:
        raise ValueError("wrong target length")
    for operation in certificate["operations"]:
        op, *args = operation
        if op == "rs":
            i, j = args
            target[i], target[j] = target[j], target[i]
        elif op == "ra":
            dest, source, multiplier = args
            target[dest] += multiplier * target[source]
        elif op == "rn":
            target[args[0]] *= -1
    diagonal = certificate["diagonal"]
    return (all(target[i] % value == 0 for i, value in enumerate(diagonal)) and
            all(value == 0 for value in target[len(diagonal):]))
