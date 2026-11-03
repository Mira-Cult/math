#!/usr/bin/env python3
"""Exact controls for the universal sparse signed-kernel frame.

The asymptotic theorem is hyperk_full_controller.md.  Finite matrices here
check the common-frame identity, independent-column sampling, exact norm
bounds, and local physicalization.  They are not full prime arrangements.
Python 3.11+; standard library only.  No stochastic test is used as proof.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import permutations, product
from math import comb
from random import Random

from hyperk_incidence import signed_blocks
from hyperk_kernel_research import (
    add, block_collections, blocks_on, clean, coordinate_pairs,
    full_signed_signature, product_tensor, pure_selector, selector_invoices,
)
from hyperk_controller import first_odd_primes, matched_pairs, prime_trial


def require(condition, message):
    if not condition:
        raise AssertionError(message)


class NormalForm:
    """Monic division for an arbitrary injection of designated marker orbits."""

    def __init__(self, d, n, labels):
        if d < 1 or n < 3 or n % 2 != 1:
            raise ValueError("positive dimension and odd n>=3 required")
        self.d = d
        self.values = tuple(range(-(n // 2), n // 2 + 1))
        self.blocks = tuple(signed_blocks(d))
        if (len(labels) != len(self.blocks) or len(set(labels)) != len(labels)
                or any(type(x) is not int or not 1 <= x <= n // 2 for x in labels)):
            raise ValueError("distinct positive marker orbit labels required")
        self.labels = dict(zip(self.blocks, labels))
        self.marker_orbits = set(labels)
        self.transitions = 0
        self.nonmarker_transitions = 0
        self._normal = lru_cache(None)(self._normal_uncached)

    def active(self, point):
        return tuple(key for key in self.blocks
                     if all(point[i] == sign * self.labels[key]
                            for i, sign in zip(*key)))

    def successors(self, point):
        active = self.active(point)
        if not active:
            return ()
        key = active[0]
        coords, signs = key
        out = []
        for t in self.values:
            if t == self.labels[key]:
                continue
            changed = list(point)
            for i, sign in zip(coords, signs):
                changed[i] = sign * t
            changed = tuple(changed)
            after = self.active(changed)
            require(len(after) <= len(active), "active blocks increased")
            if abs(t) not in self.marker_orbits:
                require(len(after) < len(active), "nonmarker rewrite failed to decrease")
                self.nonmarker_transitions += 1
            self.transitions += 1
            out.append(changed)
        return tuple(out)

    def _normal_uncached(self, point):
        successors = self.successors(point)
        if not successors:
            return {point: 1}
        out = defaultdict(int)
        for changed in successors:
            for standard, coefficient in self._normal(changed).items():
                out[standard] -= coefficient
        return clean(dict(out))

    def normal(self, point):
        return self._normal(tuple(point))

    def columns(self):
        columns = defaultdict(dict)
        for point in product(self.values, repeat=self.d):
            for standard, coefficient in self.normal(point).items():
                columns[standard][point] = coefficient
        return dict(columns)

    def one_column(self, standard):
        """Evaluate one dual normal-form functional using KG support locality."""
        if self.active(standard):
            return {}

        @lru_cache(None)
        def evaluate(point):
            successors = self.successors(point)
            if not successors:
                return int(point == standard)
            return -sum(evaluate(changed) for changed in successors)

        marked = tuple(sorted({s * a for a in self.marker_orbits for s in (-1, 1)}))
        out = {}
        for point in product(*(tuple(sorted(set(marked + (x,)))) for x in standard)):
            value = evaluate(point)
            if value:
                out[point] = value
        return out


def combine(columns, coefficients):
    out = defaultdict(int)
    for key, coefficient in coefficients.items():
        if coefficient:
            for point, value in columns.get(key, {}).items():
                out[point] += coefficient * value
    return clean(dict(out))


def exact_integer_system(matrix, rhs):
    """Fraction-free elimination, followed by exact rational back substitution."""
    count = len(rhs)
    work = [list(row) + [value] for row, value in zip(matrix, rhs)]
    require(all(len(row) == count + 1 for row in work), "nonsquare system")
    previous = 1
    for pivot_column in range(count - 1):
        pivot_row = next((i for i in range(pivot_column, count)
                          if work[i][pivot_column]), None)
        require(pivot_row is not None, "singular sampled kernel operator")
        work[pivot_column], work[pivot_row] = work[pivot_row], work[pivot_column]
        pivot = work[pivot_column][pivot_column]
        for i in range(pivot_column + 1, count):
            coefficient = work[i][pivot_column]
            for j in range(pivot_column + 1, count + 1):
                numerator = work[i][j] * pivot - coefficient * work[pivot_column][j]
                require(numerator % previous == 0, "fraction-free division was not exact")
                work[i][j] = numerator // previous
            work[i][pivot_column] = 0
        previous = pivot
    answer = [Fraction(0)] * count
    for i in range(count - 1, -1, -1):
        require(work[i][i], "singular final pivot")
        answer[i] = (Fraction(work[i][-1]) - sum(work[i][j] * answer[j]
                                                for j in range(i + 1, count))) / work[i][i]
    require(all(sum(a * x for a, x in zip(row, answer)) == value
                for row, value in zip(matrix, rhs)), "exact solve did not reconstruct")
    return answer


def allocate_common_selectors(d, excluded, start=1):
    """One auxiliary alphabet shared by all roots of one compact column."""
    used = set(excluded)
    cursor = start

    def take(count):
        nonlocal cursor
        found = []
        while len(found) < count:
            if cursor not in used:
                found.append(cursor)
                used.add(cursor)
            cursor += 1
        return tuple(found)

    anchors = take(d)
    selectors = {}
    for block in blocks_on(tuple(range(d)), signed=True):
        coords, signs = block
        template, alphabet = pure_selector(len(coords))
        labels = take(alphabet)
        selectors[block] = {
            tuple(sign * labels[t - 1] for sign, t in zip(signs, point)): value
            for point, value in template.items()
        }
    return anchors, selectors


def projected_star(root, anchors, selectors):
    d = len(root)
    require(len(set(map(abs, anchors))) == d, "anchors reuse a reflection orbit")
    require(set(map(abs, anchors)).isdisjoint(map(abs, root)), "anchor meets root")
    beta = {}
    for block in selectors:
        coords, signs = block
        t = root[coords[0]]
        beta[block] = int(all(root[i] == sign * t for i, sign in zip(coords, signs)))
    out = {}
    for pi in block_collections(d, signed=True):
        if any(not beta[block] for block in pi):
            continue
        covered = {i for coords, _ in pi for i in coords}
        factors = [(coords, selectors[(coords, signs)]) for coords, signs in pi]
        factors += [((i,), {(root[i],): 1, (anchors[i],): -1})
                    for i in range(d) if i not in covered]
        term = product_tensor(factors, d)
        require(not out.keys() & term.keys(), "projector pieces overlap")
        multiplier = (-1) ** len(pi)
        out.update({point: multiplier * value for point, value in term.items()})
    require(set(out.values()) <= {-1, 1}, "nonunit physical column")
    require(not full_signed_signature(out, d), "projected star leaves signed trace")
    return out


def physicalize(column, d, start=1):
    require(not full_signed_signature(column, d), "input is not a full kernel tensor")
    excluded = {abs(v) for point in column for v in point}
    anchors, selectors = allocate_common_selectors(d, excluded, start)
    terms = [(coefficient, projected_star(point, anchors, selectors))
             for point, coefficient in column.items()]
    reconstructed = {}
    for coefficient, template in terms:
        reconstructed = add(reconstructed, template, coefficient)
    require(reconstructed == column, "common projector failed exact reconstruction")
    return terms


def partial_prime_switch(template, d, gap=6):
    pairs = coordinate_pairs(template, d, 0)
    pool = first_odd_primes(max(128, len(pairs) * 64))
    values = matched_pairs(pool, gap, len(pairs))
    before, after = {}, {}
    for (positive, negative), (lo, hi) in zip(pairs, values):
        before[positive], before[negative] = lo, hi
        after[positive], after[negative] = hi, lo
    require(len(set(before.values())) == len(before), "duplicate prime endpoint")
    require(Counter(before.values()) == Counter(after.values()), "pool changed in switch")
    require(all(prime_trial(p) and p != 2 for p in before.values()), "composite endpoint")
    delta = {point: after[point] - before[point] for point in before}
    require(delta == {point: gap * value for point, value in template.items()},
            "wrong physical increment")
    require(not full_signed_signature(delta, d), "physical switch changes a full line")
    return len(pairs)


def sampled_operator_check(d, n, samples, seed):
    """Exact finite norm bounds; every common injection is enumerated."""
    blocks = tuple(signed_blocks(d))
    injections = tuple(permutations(range(1, n // 2 + 1), len(blocks)))
    cells = tuple(product(range(-(n // 2), n // 2 + 1), repeat=d))
    index = {point: i for i, point in enumerate(cells)}
    bases = []
    transition_count = 0
    incoming_sum = Counter()
    for labels in injections:
        form = NormalForm(d, n, labels)
        columns = form.columns()
        for column in columns.values():
            require(not full_signed_signature(column, d), "KG column leaves a signed trace")
            incoming_sum.update(column.keys())
        bases.append(columns)
        transition_count += form.transitions

    coefficient_source = {point: (17 * i + 5) % 9 - 4
                          for i, point in enumerate(cells)}
    test_tensor = combine(bases[0], coefficient_source)
    require(test_tensor, "zero test tensor")
    for basis in bases:
        require(combine(basis, test_tensor) == test_tensor, "common frame is not identity")

    size = len(cells)
    mean_numerator = [[0] * size for _ in cells]
    for basis in bases:
        for root, column in basis.items():
            v = index[root]
            for point, value in column.items():
                mean_numerator[index[point]][v] += value

    rng = Random(seed)
    numerator = [[0] * size for _ in cells]
    row_degree = Counter()
    for root in cells:
        v = index[root]
        for _ in range(samples):
            column = bases[rng.randrange(len(bases))].get(root, {})
            row_degree.update(column.keys())
            for point, value in column.items():
                numerator[index[point]][v] += value

    count = len(bases)
    denominator = samples * count
    difference = [[count * numerator[i][j] - samples * mean_numerator[i][j]
                   for j in range(size)] for i in range(size)]
    norm_inf = Fraction(max(sum(abs(x) for x in row) for row in difference), denominator)
    norm_one = Fraction(max(sum(abs(difference[i][j]) for i in range(size))
                            for j in range(size)), denominator)
    spectral_square_bound = norm_one * norm_inf
    require(spectral_square_bound < 1, "finite sampled operator has no certified contraction")
    # A common-frame average fixes the kernel exactly, while independent columns
    # usually do not.  The nonzero residual is a deliberate negative control.
    sampled_image = {}
    for i, point in enumerate(cells):
        value = sum(numerator[i][j] * test_tensor.get(root, 0)
                    for j, root in enumerate(cells))
        if value:
            sampled_image[point] = Fraction(value, samples)
    require(sampled_image != test_tensor, "negative-control sample unexpectedly exact")
    require(not full_signed_signature(sampled_image, d), "sampled image leaves kernel")

    # Solve A z=D exactly in fixed standard coordinates.  This is a finite
    # rational witness, independent of floating-point eigenvalue routines.
    standards = tuple(sorted(bases[0]))
    source = {point: 1_000_003 * value for point, value in test_tensor.items()}
    kernel_matrix = []
    for standard in standards:
        i = index[standard]
        kernel_matrix.append([
            sum(numerator[i][index[point]] * value for point, value in bases[0][root].items())
            for root in standards
        ])
    coordinates = exact_integer_system(kernel_matrix,
                                       [samples * source.get(root, 0) for root in standards])
    inverse_tensor = combine(bases[0], dict(zip(standards, coordinates)))
    require(not full_signed_signature(inverse_tensor, d), "real inverse left kernel")
    for i, point in enumerate(cells):
        image = sum(numerator[i][j] * inverse_tensor.get(root, 0)
                    for j, root in enumerate(cells)) / samples
        require(image == source.get(point, 0), "sampled real frame not exact")

    # An equivalent valid rounding rounds each KG-column coefficient first;
    # its subsequent unit physicalization has integer multiplicities.
    rounded_coefficients = {
        point: (inverse_tensor.get(point, Fraction(0)) / samples + Fraction(1, 2)).numerator
        // (inverse_tensor.get(point, Fraction(0)) / samples + Fraction(1, 2)).denominator
        for point in cells
    }
    rounded_image = {}
    remainder = {}
    row_rounding_bound = Fraction(0)
    for i, point in enumerate(cells):
        value = sum(numerator[i][j] * rounded_coefficients[root]
                    for j, root in enumerate(cells))
        if value:
            rounded_image[point] = value
        if source.get(point, 0) - value:
            remainder[point] = source.get(point, 0) - value
        # Triangle bound on the pre-averaged signed columns, using C as
        # the observed maximum column coefficient in this finite fixture.
    coefficient_cap = max(abs(value) for basis in bases for column in basis.values()
                          for value in column.values())
    row_rounding_bound = Fraction(coefficient_cap * max(row_degree.values()), 2)
    require(not full_signed_signature(rounded_image, d), "rounded image left kernel")
    require(not full_signed_signature(remainder, d), "integer remainder left kernel")
    require(all(type(value) is int for value in remainder.values()), "noninteger remainder")
    require(max(map(abs, remainder.values()), default=0) <= row_rounding_bound,
            "rounding exceeded the point-load bound")
    return {
        "dimension": d, "order": n, "common_injections": count,
        "samples_per_input_cell": samples, "active_rewrites_checked": transition_count,
        "norm_one": str(norm_one), "norm_infinity": str(norm_inf),
        "spectral_norm_squared_upper_bound": str(spectral_square_bound),
        "maximum_sampled_point_degree": max(row_degree.values()),
        "maximum_expected_incoming_support": str(Fraction(max(incoming_sum.values()), count)),
        "exact_common_frame_identities": count,
        "exact_real_inverse_replayed": True,
        "integer_rounding_remainder_norm": max(map(abs, remainder.values()), default=0),
        "integer_rounding_point_load_bound": str(row_rounding_bound),
    }


def run_self_test():
    reports = []
    reports.append(sampled_operator_check(1, 9, 2048, 89131))
    reports.append(sampled_operator_check(2, 9, 8192, 772349))

    local_columns = []
    for d, n, roots in [
        (1, 9, [(0,), (-1,), (4,)]),
        (2, 11, [(0, 0), (5, 5), (5, -5), (5, 0), (-2, 5)]),
        (3, 31, [(0, 0, 0), (14, 14, 14), (14, -14, 0), (14, 15, -14)]),
    ]:
        labels = tuple(range(1, len(tuple(signed_blocks(d))) + 1))
        for root in roots:
            form = NormalForm(d, n, labels)
            column = form.one_column(root)
            require(column, "chosen fixture is not standard")
            require(not full_signed_signature(column, d), "sparse KG column failed")
            terms = physicalize(column, d, start=40)
            pairings = 0
            for _, template in terms:
                for axis in range(d):
                    coordinate_pairs(template, d, axis)
                    pairings += 1
            chosen = max((template for _, template in terms), key=len)
            prime_pairs = partial_prime_switch(chosen, d)
            local_columns.append({
                "dimension": d, "root": root, "KG_support": len(column),
                "KG_maximum_coefficient": max(map(abs, column.values())),
                "physical_templates": len(terms),
                "largest_physical_support": max(len(template) for _, template in terms),
                "coordinate_pairings_checked": pairings,
                "partial_prime_switch_pairs": prime_pairs,
            })

    # The exact monotonicity must hold well beyond the orders used in matrices.
    rng = Random(412721)
    higher = []
    for d in (4, 5, 6):
        blocks = tuple(signed_blocks(d))
        h = len(blocks)
        form = NormalForm(d, 2 * h + 7, tuple(range(1, h + 1)))
        for _ in range(40):
            point = [rng.choice(form.values) for _ in range(d)]
            coords, signs = rng.choice(blocks)
            for i, sign in zip(coords, signs):
                point[i] = sign * form.labels[(coords, signs)]
            form.successors(tuple(point))
        higher.append({"dimension": d, "active_rewrites_checked": form.transitions,
                       "strict_nonmarker_decreases": form.nonmarker_transitions})

    rejected = 0
    for labels in ((0, 2, 3, 4), (1, 1, 3, 4), (1, 2, 3, 6)):
        try:
            NormalForm(2, 11, labels)
        except ValueError:
            rejected += 1
        else:
            raise AssertionError("bad marker injection accepted")
    try:
        physicalize({(0, 0): 1}, 2)
    except AssertionError:
        rejected += 1
    else:
        raise AssertionError("nonkernel column accepted")
    good = local_columns[0]
    require(good["dimension"] == 1, "fixture bookkeeping")
    source = {(1, 3): 1, (1, 4): -1, (2, 3): -1, (2, 4): 1}
    require(not full_signed_signature(source, 2), "generic source not in kernel")
    incoherent = {}
    for j, (root, coefficient) in enumerate(source.items()):
        anchors, selectors = allocate_common_selectors(2, {1, 2, 3, 4}, 20 + 30 * j)
        incoherent = add(incoherent, projected_star(root, anchors, selectors), coefficient)
    require(incoherent != source, "incoherent-marker negative control failed")
    rejected += 1
    for _, template in physicalize(source, 2, start=200):
        damaged = dict(template)
        first = next(iter(damaged))
        damaged[first] *= -1
        require(full_signed_signature(damaged, 2), "wrong-sign control missed")
        rejected += 1
        break

    alphabets, supports = selector_invoices(6)
    invoices = []
    for d in range(1, 7):
        q_d = 0
        f_d = 0
        for pi in block_collections(d, signed=True):
            union = sum(len(coords) for coords, _ in pi)
            cost = 1
            for coords, _ in pi:
                cost *= supports[len(coords)]
            q_d += 2 ** (d - union) * cost
            f_d += 6 ** len(pi) * 7 ** (d - union) * cost
        a_d = d + sum(comb(d, b) * 2 ** (b - 1) * alphabets[b]
                      for b in range(2, d + 1))
        invoices.append({"dimension": d, "auxiliary_orbits": a_d,
                         "unit_template_support_bound": q_d,
                         "physical_expected_row_factor": f_d})

    return {"finite_uniform_operators": reports, "local_physical_columns": local_columns,
            "higher_dimension_active_block_controls": higher,
            "symbolic_invoices": invoices, "malformed_or_false_shortcuts_rejected": rejected,
            "scope": "Exact kernel and partial-switch diagnostics; no full prime arrangement."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true", help="run all exact controls (default)")
    parser.parse_args()
    import json
    print(json.dumps(run_self_test(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
