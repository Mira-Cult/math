"""Exact incidence and signed-integer capacity tools; no prime-pool inference.

All arrays are row-major flat sequences unless explicitly called matrices.
This module uses only the Python standard library.  Rational lifting and
rounding can be expensive; the routines are reference implementations.
"""

from collections import deque
from fractions import Fraction
from itertools import combinations, product
from math import comb, isqrt


def flat_index(coords, n):
    out = 0
    for coordinate in coords:
        out = n * out + coordinate
    return out


def sum_axis(values, n, dimension, axis):
    if len(values) != n ** dimension or not 0 <= axis < dimension:
        raise ValueError("invalid tensor shape or axis")
    out = [0] * n ** (dimension - 1)
    for coords in product(range(n), repeat=dimension):
        rest = coords[:axis] + coords[axis + 1:]
        out[flat_index(rest, n)] += values[flat_index(coords, n)]
    return out


def axis_sums(values, n, dimension):
    return [sum_axis(values, n, dimension, d) for d in range(dimension)]


def compatible_axes(targets, n, dimension):
    if len(targets) != dimension or any(
        len(v) != n ** (dimension - 1) for v in targets
    ):
        return False
    for d in range(dimension):
        for e in range(d + 1, dimension):
            left = sum_axis(targets[d], n, dimension - 1, e - 1)
            right = sum_axis(targets[e], n, dimension - 1, d)
            if left != right:
                return False
    return True


def balanced_axis_lift(targets, n, dimension):
    """Inclusion-exclusion rational preimage, or ValueError if incompatible."""
    if not compatible_axes(targets, n, dimension):
        raise ValueError("incompatible axis targets")
    marginals = []
    for count in range(1, dimension + 1):
        for removed in combinations(range(dimension), count):
            d = removed[0]
            remaining = [e for e in range(dimension) if e != d]
            data = list(targets[d])
            for e in removed[1:]:
                axis = remaining.index(e)
                data = sum_axis(data, n, len(remaining), axis)
                remaining.remove(e)
            marginals.append((remaining, data, Fraction((-1) ** (count + 1), n ** count)))
    out = []
    for coords in product(range(n), repeat=dimension):
        out.append(sum(
            factor * data[flat_index(tuple(coords[d] for d in remaining), n)]
            for remaining, data, factor in marginals
        ))
    return out


class _Flow:
    """Integer Dinic flow, used only for finite bipartite matrix rounding."""

    def __init__(self, count):
        self.adj = [[] for _ in range(count)]

    def edge(self, source, target, capacity):
        forward = [target, capacity, len(self.adj[target])]
        backward = [source, 0, len(self.adj[source])]
        self.adj[source].append(forward)
        self.adj[target].append(backward)
        return forward

    def maximum(self, source, sink):
        total = 0
        while True:
            level = [-1] * len(self.adj)
            level[source] = 0
            queue = deque([source])
            while queue:
                u = queue.popleft()
                for v, capacity, _ in self.adj[u]:
                    if capacity and level[v] < 0:
                        level[v] = level[u] + 1
                        queue.append(v)
            if level[sink] < 0:
                return total
            cursor = [0] * len(self.adj)

            def augment(u, bound):
                if u == sink:
                    return bound
                while cursor[u] < len(self.adj[u]):
                    edge = self.adj[u][cursor[u]]
                    v, capacity, reverse = edge
                    if capacity and level[v] == level[u] + 1:
                        sent = augment(v, min(bound, capacity))
                        if sent:
                            edge[1] -= sent
                            self.adj[v][reverse][1] += sent
                            return sent
                    cursor[u] += 1
                return 0

            while True:
                sent = augment(source, 10 ** 100)
                if not sent:
                    break
                total += sent


def _integer(value):
    value = Fraction(value)
    if value.denominator != 1:
        raise ValueError("nonintegral required margin")
    return value.numerator


def round_matrix(matrix):
    """Round to floors/ceilings, preserving integral row and column margins."""
    rows = len(matrix)
    cols = len(matrix[0]) if rows else 0
    if not rows or not cols or any(len(row) != cols for row in matrix):
        raise ValueError("nonempty rectangular matrix required")
    rational = [[Fraction(x) for x in row] for row in matrix]
    floors = [[x.numerator // x.denominator for x in row] for row in rational]
    row_demands = [
        _integer(sum(rational[i]) - sum(floors[i])) for i in range(rows)
    ]
    col_demands = [
        _integer(sum(rational[i][j] - floors[i][j] for i in range(rows)))
        for j in range(cols)
    ]
    source, sink = rows + cols, rows + cols + 1
    flow = _Flow(sink + 1)
    for i, demand in enumerate(row_demands):
        flow.edge(source, i, demand)
    for j, demand in enumerate(col_demands):
        flow.edge(rows + j, sink, demand)
    handles = {}
    for i in range(rows):
        for j in range(cols):
            if rational[i][j] != floors[i][j]:
                handles[i, j] = flow.edge(i, rows + j, 1)
    if flow.maximum(source, sink) != sum(row_demands):
        raise AssertionError("fractional feasible flow lacked integral maximum")
    return [[
        floors[i][j] + (1 - handles[i, j][1] if (i, j) in handles else 0)
        for j in range(cols)
    ] for i in range(rows)]


def split_zero_matrix(matrix, pieces):
    """Exact zero-margin splitting, each entry floor/ceiling of average."""
    n = len(matrix)
    if pieces < 1 or any(len(row) != n for row in matrix):
        raise ValueError("positive count and square matrix required")
    if any(sum(row) for row in matrix) or any(
        sum(matrix[i][j] for i in range(n)) for j in range(n)
    ):
        raise ValueError("zero margins required")
    fixed = [[_integer(x) // pieces for x in row] for row in matrix]
    residual = [[matrix[i][j] - pieces * fixed[i][j] for j in range(n)] for i in range(n)]
    out = []
    for remaining in range(pieces, 0, -1):
        binary = round_matrix([[Fraction(x, remaining) for x in row] for row in residual])
        out.append([[fixed[i][j] + binary[i][j] for j in range(n)] for i in range(n)])
        residual = [[residual[i][j] - binary[i][j] for j in range(n)] for i in range(n)]
    assert all(x == 0 for row in residual for x in row)
    return out


def _split_zero_tensor(values, pieces, n, dimension):
    if pieces == 1:
        return [list(values)]
    left_count = pieces // 2
    left = round_axis_tensor([Fraction(x * left_count, pieces) for x in values], n, dimension)
    right = [x - y for x, y in zip(values, left)]
    return (
        _split_zero_tensor(left, left_count, n, dimension)
        + _split_zero_tensor(right, pieces - left_count, n, dimension)
    )


def rounding_constant(dimension):
    if dimension <= 2:
        return 1
    return 2 * 5 ** (dimension - 3)


def round_axis_tensor(values, n, dimension):
    """Preserve all integral axis marginals, with dimension-only error."""
    values = [Fraction(x) for x in values]
    targets = axis_sums(values, n, dimension)
    if any(Fraction(x).denominator != 1 for row in targets for x in row):
        raise ValueError("all axis margins must be integral")
    if dimension == 1:
        out = [x.numerator // x.denominator for x in values]
        demand = _integer(sum(values) - sum(out))
        fractional_positions = [i for i, x in enumerate(values) if x != out[i]]
        for i in fractional_positions[:demand]:
            out[i] += 1
        return out
    if dimension == 2:
        matrix = [values[i * n:(i + 1) * n] for i in range(n)]
        return [x for row in round_matrix(matrix) for x in row]
    rounded_slices = []
    for k in range(n):
        rounded_slices.append(round_axis_tensor(values[k::n], n, dimension - 1))
    residual = [
        _integer(targets[-1][i]) - sum(rounded_slices[k][i] for k in range(n))
        for i in range(n ** (dimension - 1))
    ]
    if dimension == 3:
        matrix = [residual[i * n:(i + 1) * n] for i in range(n)]
        corrections = [[x for row in part for x in row] for part in split_zero_matrix(matrix, n)]
    else:
        corrections = _split_zero_tensor(residual, n, n, dimension - 1)
    out = [
        rounded_slices[k][i] + corrections[k][i]
        for i in range(n ** (dimension - 1)) for k in range(n)
    ]
    assert axis_sums(out, n, dimension) == targets
    return out


def integer_axis_lift(targets, n, dimension):
    return round_axis_tensor(balanced_axis_lift(targets, n, dimension), n, dimension)


def axis_lines(n, dimension):
    edges = set()
    for axis in range(dimension):
        for fixed in product(range(n), repeat=dimension - 1):
            edge = []
            for t in range(n):
                coords = fixed[:axis] + (t,) + fixed[axis:]
                edge.append(flat_index(coords, n))
            edges.add(tuple(sorted(edge)))
    return tuple(sorted(edges))


def signed_sections(n, dimension, rank):
    """Brute symbol-map generator; deduplicates subsets independently of (10)."""
    if not 1 <= rank <= dimension:
        raise ValueError("invalid section dimension")
    # 0,...,n-1 are fixed; n+2*j and n+2*j+1 are parameter j, forward/reverse.
    edges = set()
    for symbols in product(range(n + 2 * rank), repeat=dimension):
        used = {(symbol - n) // 2 for symbol in symbols if symbol >= n}
        if used != set(range(rank)):
            continue
        edge = []
        for parameters in product(range(n), repeat=rank):
            coords = []
            for symbol in symbols:
                if symbol < n:
                    coords.append(symbol)
                else:
                    parameter, reverse = divmod(symbol - n, 2)
                    value = parameters[parameter]
                    coords.append(n - 1 - value if reverse else value)
            edge.append(flat_index(coords, n))
        edges.add(tuple(sorted(edge)))
    return tuple(sorted(edges))


def section_count(n, dimension, rank):
    stirling = [[0] * (dimension + 1) for _ in range(dimension + 1)]
    stirling[0][0] = 1
    for k in range(1, dimension + 1):
        for r in range(1, k + 1):
            stirling[k][r] = stirling[k - 1][r - 1] + r * stirling[k - 1][r]
    return sum(
        comb(dimension, k) * n ** (dimension - k) * stirling[k][rank] * 2 ** (k - rank)
        for k in range(rank, dimension + 1)
    )


def cyclic_windows(n, offsets=None):
    offsets = range(n) if offsets is None else sorted(set(offsets))
    if any(not 0 <= r < n for r in offsets):
        raise ValueError("offset outside one period")
    return tuple(
        tuple(sorted((r + k * n + j) % (n * n) for j in range(n)))
        for r in offsets for k in range(n)
    )


def cyclic_tracks(window_sums, n):
    if len(window_sums) != n * n:
        raise ValueError("wrong window count")
    partition_totals = [sum(window_sums[r::n]) for r in range(n)]
    if len(set(partition_totals)) != 1:
        raise ValueError("offset-partition totals differ")
    tracks = []
    for r in range(n):
        track = [0]
        for k in range(n - 1):
            i = r + k * n
            track.append(track[-1] + window_sums[(i + 1) % (n * n)] - window_sums[i])
        tracks.append(track)
    return tracks


def cyclic_box_intervals(window_sums, n, lower, upper):
    tracks = cyclic_tracks(window_sums, n)
    intervals = [(lower - min(h), upper - max(h)) for h in tracks]
    feasible = (
        all(lo <= hi for lo, hi in intervals)
        and sum(lo for lo, _ in intervals) <= window_sums[0] <= sum(hi for _, hi in intervals)
    )
    return feasible, intervals, tracks


def cyclic_integer_lift(window_sums, n, lower=None, upper=None):
    window_sums = [_integer(x) for x in window_sums]
    if (lower is None) != (upper is None):
        raise ValueError("specify both entry bounds or neither")
    if lower is None:
        tracks = cyclic_tracks(window_sums, n)
        bases = [window_sums[0]] + [0] * (n - 1)
    else:
        lower, upper = _integer(lower), _integer(upper)
        feasible, intervals, tracks = cyclic_box_intervals(window_sums, n, lower, upper)
        if not feasible:
            raise ValueError("target outside bounded numeric region")
        bases = [lo for lo, _ in intervals]
        remaining = window_sums[0] - sum(bases)
        for r, (lo, hi) in enumerate(intervals):
            added = min(remaining, hi - lo)
            bases[r] += added
            remaining -= added
        assert remaining == 0
    return [bases[r] + tracks[r][k] for k in range(n) for r in range(n)]


def prime_field_lines(prime):
    """All affine lines over F_p for prime p; not a prime-power-field package."""
    if prime < 2 or any(prime % d == 0 for d in range(2, isqrt(prime) + 1)):
        raise ValueError("prime modulus required")
    n = prime
    classes = [tuple(tuple(n * x + y for y in range(n)) for x in range(n))]
    for slope in range(n):
        classes.append(tuple(
            tuple(n * x + (slope * x + intercept) % n for x in range(n))
            for intercept in range(n)
        ))
    return tuple(classes)


def prime_zero_sum_indices(values, prime):
    """Construct q indices summing to zero mod prime q from 2q-1 entries."""
    if prime < 2 or any(prime % d == 0 for d in range(2, isqrt(prime) + 1)):
        raise ValueError("prime modulus required")
    if len(values) < 2 * prime - 1:
        raise ValueError("at least 2q-1 entries required")
    ordered = sorted((values[i] % prime, i) for i in range(2 * prime - 1))
    for i in range(prime - 1):
        if ordered[i][0] == ordered[i + prime - 1][0]:
            return tuple(index for _, index in ordered[i:i + prime])
    reachable = {ordered[-1][0]: (ordered[-1][1],)}
    for i in range(prime - 1):
        next_reachable = {}
        for residue, witness in reachable.items():
            for value, index in (ordered[i], ordered[i + prime - 1]):
                next_reachable.setdefault((residue + value) % prime, witness + (index,))
        reachable = next_reachable
    assert 0 in reachable
    return reachable[0]


def prescribed_length_zero_sum(values, length, prime):
    """Select n entries with sum divisible by q|n from n+q-1 entries."""
    if prime < 2 or length < 1 or length % prime or len(values) < length + prime - 1:
        raise ValueError("q must divide n and at least n+q-1 entries are needed")
    remaining = list(enumerate(values))
    chosen = []
    for _ in range(length // prime):
        positions = prime_zero_sum_indices([value for _, value in remaining], prime)
        chosen.extend(remaining[i][0] for i in positions)
        removed = set(positions)
        remaining = [entry for i, entry in enumerate(remaining) if i not in removed]
    assert len(set(chosen)) == length and sum(values[i] for i in chosen) % prime == 0
    return tuple(chosen)


def exact_rank(rows):
    matrix = [[Fraction(x) for x in row] for row in rows]
    if not matrix:
        return 0
    rank = 0
    for col in range(len(matrix[0])):
        pivot = next((r for r in range(rank, len(matrix)) if matrix[r][col]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        leading = matrix[rank][col]
        matrix[rank] = [x / leading for x in matrix[rank]]
        for r in range(rank + 1, len(matrix)):
            if matrix[r][col]:
                factor = matrix[r][col]
                matrix[r] = [a - factor * b for a, b in zip(matrix[r], matrix[rank])]
        rank += 1
        if rank == len(matrix):
            break
    return rank


def incidence_rows(edges, cell_count):
    return [[int(cell in edge) for cell in range(cell_count)] for edge in edges]


def _transpose(matrix):
    return list(map(list, zip(*matrix)))


def _multiply(left, right):
    right_columns = _transpose(right)
    return [[sum(x * y for x, y in zip(row, col)) for col in right_columns] for row in left]


def _inverse(matrix):
    n = len(matrix)
    work = [[Fraction(x) for x in row] + [Fraction(i == j) for j in range(n)] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next((r for r in range(col, n) if work[r][col]), None)
        if pivot is None:
            raise ValueError("singular matrix")
        work[col], work[pivot] = work[pivot], work[col]
        leading = work[col][col]
        work[col] = [x / leading for x in work[col]]
        for r in range(n):
            if r != col and work[r][col]:
                factor = work[r][col]
                work[r] = [a - factor * b for a, b in zip(work[r], work[col])]
    return [row[n:] for row in work]


def graph_incidence(n, edges):
    matrix = [[0] * len(edges) for _ in range(n)]
    for e, (u, v) in enumerate(edges):
        if not (0 <= u < n and 0 <= v < n) or u == v:
            raise ValueError("loopless graph on specified vertices required")
        matrix[u][e] = 1
        matrix[v][e] = -1
    return matrix


def _tree_inverse(n, edges):
    adjacency = [[] for _ in range(n)]
    for e, (u, v) in enumerate(edges):
        adjacency[u].append((v, e))
        adjacency[v].append((u, e))
    root = n - 1
    parent = {root: None}
    order = [root]
    parent_edge = {}
    for u in order:
        for v, e in adjacency[u]:
            if v not in parent:
                parent[v] = u
                parent_edge[v] = e
                order.append(v)
    if len(order) != n:
        raise ValueError("connected graph required")
    descendants = [{v} for v in range(n)]
    for v in reversed(order[1:]):
        descendants[parent[v]].update(descendants[v])
    matrix = [[0] * n for _ in edges]
    for v in order[1:]:
        e = parent_edge[v]
        sign = 1 if edges[e][0] == v else -1
        for u in descendants[v]:
            matrix[e][u] = sign
    return matrix


def graph_product_lift(matrix, edges):
    """Exact integer rectangle coefficients using a rational graph inverse.

    Works for any connected loopless graph; the expander spectral estimate
    requires the additional degree and gap hypotheses in the manuscript.
    Returns integer coefficients plus the exact real inverse norm.
    """
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("square correction matrix required")
    if any(sum(row) for row in matrix) or any(sum(matrix[i][j] for i in range(n)) for j in range(n)):
        raise ValueError("zero row and column margins required")
    matrix = [[_integer(x) for x in row] for row in matrix]
    incidence = graph_incidence(n, edges)
    laplacian = _multiply(incidence, _transpose(incidence))
    regularized = [[Fraction(laplacian[i][j]) + Fraction(1, n) for j in range(n)] for i in range(n)]
    inverse = _multiply(_transpose(incidence), _inverse(regularized))
    real_coefficients = _multiply(_multiply(inverse, matrix), _transpose(inverse))
    rounded = [[(x + Fraction(1, 2)).numerator // (x + Fraction(1, 2)).denominator for x in row] for row in real_coefficients]
    applied = _multiply(_multiply(incidence, rounded), _transpose(incidence))
    residual = [[matrix[i][j] - applied[i][j] for j in range(n)] for i in range(n)]
    tree = _tree_inverse(n, edges)
    repair = _multiply(_multiply(tree, residual), _transpose(tree))
    result = [[a + b for a, b in zip(row, fixing)] for row, fixing in zip(rounded, repair)]
    assert _multiply(_multiply(incidence, result), _transpose(incidence)) == matrix
    return result, max(sum(abs(x) for x in row) for row in inverse)
