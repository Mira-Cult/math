#!/usr/bin/env python3
"""Exact controls for the half-coordinate theorem, not an asymptotic prover.

The finite marker graph is a routed path. It checks integer/residue identities
and disjoint support; it is not offered as an expander capacity certificate.
The imported majority controller source remains frozen and unchanged.
"""

from collections import Counter, defaultdict
from copy import deepcopy
from itertools import product
from math import comb
from random import Random
import json

from hyperk_controller import (
    formula_signature, first_odd_primes, matched_pairs, prime_trial,
    require, sparse_signature, tensor,
)


def add_scaled(target, source, scalar):
    for point, value in source.items():
        target[point] = target.get(point, 0) + scalar * value
        if target[point] == 0:
            del target[point]


def signs(d):
    return tuple((1,) + tail for tail in product((-1, 1), repeat=d - 1))


def body_traces(values, d):
    result = {}
    for pattern in signs(d):
        result[pattern] = sum(
            value for point, value in values.items()
            if all(point[i] == pattern[i] * point[0] for i in range(d))
        )
    return result


def zero_margins(values, d, modulus=None):
    for axis in range(d):
        margins = defaultdict(int)
        for point, value in values.items():
            margins[point[:axis] + point[axis + 1:]] += value
        require(all(v == 0 if modulus is None else v % modulus == 0
                    for v in margins.values()), "nonzero axis margin")


def check_body_kernel(values, d, modulus=None):
    zero_margins(values, d, modulus)
    require(all(v == 0 if modulus is None else v % modulus == 0
                for v in body_traces(values, d).values()), "nonzero body trace")


def component_sum(components, require_disjoint=True):
    values = {}
    seen = set()
    for coefficient, factors in components:
        require(coefficient in (-1, 1), "component coefficient must be a sign")
        term = tensor(factors)
        if require_disjoint:
            require(not (seen & term.keys()), "overlapping checkerboard pieces")
        seen.update(term)
        add_scaled(values, term, coefficient)
    require(all(v in (-1, 1) for v in values.values()), "nonunit template entry")
    return values


def reflected_unit_selector(pattern, labels):
    require(len(labels) == len(pattern) + 1, "selector alphabet size")
    require(all(x > 0 for x in labels) and len(set(labels)) == len(labels), "noncentral distinct selector labels")
    common = labels[0]
    return tuple((s * common, s * other) for s, other in zip(pattern, labels[1:]))


def marker_projection_fixture(d, n=129):
    """Full raw product family of a path on {-1,0,1}, inside ambient I_n.

    This small subgraph is a diagnostic. All raw tensors and all marker path
    templates are explicitly represented and their exact loads are checked.
    """
    require(d >= 2 and n % 2 == 1, "fixture dimension/order")
    labels = list(range(1, (n + 1) // 2))
    rng = Random(2026110200 + d)
    use = Counter()
    markers = []
    populations = {pattern: [] for pattern in signs(d)}
    raw = []
    projected = []
    attachments = []
    graph_edges = ((-1, 0), (0, 1))

    def marker(pattern, excluded):
        chosen = []
        for _ in range(d + 1):
            options = [x for x in labels if x not in excluded and x not in chosen]
            require(options, "insufficient fixture marker labels")
            rng.shuffle(options)
            chosen.append(min(options, key=lambda x: use[x]))
        factors = reflected_unit_selector(pattern, chosen)
        values = tensor(factors)
        trace = body_traces(values, d)
        require(trace == {s: int(s == pattern) for s in signs(d)}, "marker trace vector")
        index = len(markers)
        markers.append({"factors": factors, "values": values,
                        "support": frozenset(values), "pattern": pattern})
        populations[pattern].append(index)
        use.update(chosen)
        return index, set(chosen)

    for factors in product(graph_edges, repeat=d):
        values = tensor(factors)
        raw.append(values)
        excluded = {abs(x) for factor in factors for x in factor if x}
        attached = []
        components = [(1, factors)]
        for pattern, trace in body_traces(values, d).items():
            for _ in range(abs(trace)):
                index, alphabet = marker(pattern, excluded)
                excluded |= alphabet
                sign = 1 if trace > 0 else -1
                attached.append((index, sign))
                components.append((-sign, markers[index]["factors"]))
        image = component_sum(components)
        check_body_kernel(image, d)
        projected.append({"components": components, "values": image})
        attachments.append(attached)

    for pattern in signs(d):
        for _ in range(n):
            marker(pattern, set())

    # Paths are repaired exactly as BR(d), with maximum middle use four.
    routes = {}
    all_flow_templates = []
    maximum_degree = 0
    for pattern, nodes in populations.items():
        middle_use = Counter()
        degree = Counter()
        pattern_routes = []
        for left, right in zip(nodes, nodes[1:]):
            if markers[left]["support"].isdisjoint(markers[right]["support"]):
                path = (left, right)
            else:
                candidates = [q for q in nodes if q not in (left, right)
                              and middle_use[q] < 4
                              and markers[q]["support"].isdisjoint(markers[left]["support"])
                              and markers[q]["support"].isdisjoint(markers[right]["support"])]
                require(candidates, "no fixture disjoint middle marker")
                middle = min(candidates, key=lambda q: (middle_use[q], q))
                middle_use[middle] += 1
                path = (left, middle, right)
            arcs = tuple(zip(path, path[1:]))
            pattern_routes.append(arcs)
            for u, v in arcs:
                degree[u] += 1
                degree[v] += 1
                components = [(1, markers[u]["factors"]), (-1, markers[v]["factors"])]
                values = component_sum(components)
                check_body_kernel(values, d)
                all_flow_templates.append({"components": components, "values": values})
        require(max(degree.values(), default=0) <= 10, "routed path degree")
        require(max(middle_use.values(), default=0) <= 4, "routed middle load")
        maximum_degree = max(maximum_degree, max(degree.values(), default=0))
        routes[pattern] = pattern_routes

    # Literal full-template incidence, including dormant zero-flow templates.
    # Count support incidences, including templates whose eventual flow is zero.
    incidence = Counter()
    for template in projected + all_flow_templates:
        incidence.update(template["values"].keys())
    max_marker_use = max(use.values(), default=0)
    fixture_bound = 2 ** d + 11 * max_marker_use
    require(max(incidence.values(), default=0) <= fixture_bound, "point-load bound")

    return {"d": d, "n": n, "markers": markers, "populations": populations,
            "raw": raw, "projected": projected, "attachments": attachments,
            "routes": routes, "flow_templates": all_flow_templates,
            "max_point_load": max(incidence.values(), default=0),
            "point_load_bound": fixture_bound, "max_path_degree": maximum_degree,
            "max_marker_orbit_use": max_marker_use}


def zero_trace_coefficients(fixture):
    """Nontrivial exact kernel demands, independently grouped by trace vector."""
    d = fixture["d"]
    groups = defaultdict(list)
    coefficients = [0] * len(fixture["raw"])
    rng = Random(61000 + d)
    for i, values in enumerate(fixture["raw"]):
        vector = tuple(body_traces(values, d)[s] for s in signs(d))
        first = next((x for x in vector if x), 0)
        orientation = 1 if first >= 0 else -1
        key = tuple(orientation * x for x in vector)
        groups[key].append((i, orientation))
    for vector, group in groups.items():
        if not any(vector):
            for i, _ in group:
                coefficients[i] = rng.randint(-7, 7)
            continue
        partial = 0
        for i, orientation in group[:-1]:
            value = rng.randint(-7, 7)
            coefficients[i] = orientation * value
            partial += value
        i, orientation = group[-1]
        coefficients[i] = -orientation * partial
    require(any(coefficients), "trivial fixture coefficients")
    return coefficients


def reconstruct(fixture, coefficients, modulus=None):
    d = fixture["d"]
    target, output = {}, {}
    demand = [0] * len(fixture["markers"])
    for c, raw, projected, attached in zip(coefficients, fixture["raw"],
                                          fixture["projected"], fixture["attachments"]):
        add_scaled(target, raw, c)
        add_scaled(output, projected["values"], c if modulus is None else c % modulus)
        for q, sign in attached:
            demand[q] += c * sign
    check_body_kernel(target, d, modulus)
    for pattern, nodes in fixture["populations"].items():
        total = sum(demand[q] for q in nodes)
        require(total == 0 if modulus is None else total % modulus == 0,
                "marker demand fails exact trace condition")
        prefix = 0
        for j, arcs in enumerate(fixture["routes"][pattern]):
            prefix += demand[nodes[j]]
            coefficient = prefix if modulus is None else prefix % modulus
            for u, v in arcs:
                add_scaled(output, fixture["markers"][u]["values"], coefficient)
                add_scaled(output, fixture["markers"][v]["values"], -coefficient)
    if modulus is None:
        require(output == target, "integer marker reconstruction")
    else:
        require(all((output.get(p, 0) - target.get(p, 0)) % modulus == 0
                    for p in output.keys() | target.keys()), "residue reconstruction")
    return target


def compound_delta(outer_factors, inner_template):
    require(len(outer_factors) >= 2, "native selector dimension")
    d = len(outer_factors)
    inner = component_sum(inner_template["components"])
    check_body_kernel(inner, d)
    outer_orbits = {abs(x) for f in outer_factors for x in f}
    inner_orbits = {abs(x) for point in inner for x in point}
    require(outer_orbits.isdisjoint(inner_orbits), "mixed-orbit collision")
    return {a + b: sign * value for a, sign in tensor(outer_factors).items()
            for b, value in inner.items()}


def check_compound_signature(outer_factors, inner_template):
    d = len(outer_factors)
    delta = compound_delta(outer_factors, inner_template)
    point_image = sparse_signature(delta, 2 * d)
    formula_image = {}
    for sign, inner_factors in inner_template["components"]:
        add_scaled(formula_image, formula_signature(outer_factors + inner_factors), sign)
    require(point_image == formula_image, "complete compound signature")
    native_pattern = tuple(1 if f[0] > 0 else -1 for f in outer_factors)
    require(native_pattern[0] == 1, "normalized outer sign")
    native_block = tuple(range(d))
    for line in point_image:
        require(len(line[0]) != 1, "compound changes an axis")
        if len(line[0]) >= d:
            require(line[0] == native_block and line[1] == native_pattern,
                    "compound changes protected family")
    native = {tuple(value for _, value in key[2]): value
              for key, value in point_image.items() if key[0] == native_block
              and key[1] == native_pattern}
    require(native == inner_template["values"], "wrong native compound target")
    return delta


def physical_compound(outer_factors, inner_template, gap=6):
    delta = compound_delta(outer_factors, inner_template)
    lower_cells = sorted(point for point in delta if point[0] == outer_factors[0][0])
    prime_pairs = matched_pairs(first_odd_primes(max(200, 16 * len(lower_cells))),
                                gap, len(lower_cells))
    before, pairs = {}, []
    for a, (p, q) in zip(lower_cells, prime_pairs):
        b = (outer_factors[0][1],) + a[1:]
        before[a], before[b] = ((p, q) if delta[a] == 1 else (q, p))
        pairs.append((a, b))
    m = max(abs(x) for point in delta for x in point)
    certificate = {"kind": "partial-prime-compound", "dimension": 2 * len(outer_factors),
                   "order": 2 * m + 1, "gap": gap, "outer_factors": outer_factors,
                   "components": inner_template["components"], "before": before,
                   "pairs": pairs}
    verify_physical_compound(certificate)
    return certificate


def verify_physical_compound(certificate):
    require(certificate["kind"] == "partial-prime-compound", "partial compound is not an arrangement")
    outer = certificate["outer_factors"]
    template = {"components": certificate["components"],
                "values": component_sum(certificate["components"])}
    delta = compound_delta(outer, template)
    before = certificate["before"]
    n, k, gap = certificate["order"], certificate["dimension"], certificate["gap"]
    require(k == 2 * len(outer) and n % 2 == 1, "dimension/order")
    require(set(before) == set(delta), "incorrect physical support")
    require(len(set(before.values())) == len(before), "duplicate prime entry")
    require(all(prime_trial(value) and value > 2 for value in before.values()), "nonprime endpoint")
    require(all(abs(x) <= n // 2 for point in before for x in point), "cell outside array")
    # The j-th odd prime is at least 2j+1. A stronger elementary rank upper
    # bound for a given odd prime p is its count of odd candidates <=p.
    require(all((value - 1) // 2 <= n ** k for value in before.values()),
            "prescribed first-pool membership not certified")
    after = dict(before)
    used = set()
    for a, b in certificate["pairs"]:
        require(a != b and a in before and b in before, "invalid pair")
        require(a not in used and b not in used, "reused pair cell")
        require(abs(before[a] - before[b]) == gap, "wrong pair difference")
        used.update((a, b))
        after[a], after[b] = after[b], after[a]
    require(used == set(before), "omitted paired cell")
    require(all(after[p] - before[p] == gap * value for p, value in delta.items()),
            "wrong physical orientation")
    require(set(after.values()) == set(before.values()), "not a permutation")
    return len(certificate["pairs"])


def expect_rejection(callback):
    try:
        callback()
    except (ValueError, KeyError, TypeError):
        return
    raise AssertionError("malformed control accepted")


def run_checks():
    report = {"scope": "finite templates and actual partial trades; not full arrangements",
              "marker_graph": "bounded-degree routed paths, not expander certificates"}
    fixture_reports = []
    signature_cases = 0
    physical_pairs = []
    last_certificate = None
    for d in (2, 3, 4):
        fixture = marker_projection_fixture(d)
        coefficients = zero_trace_coefficients(fixture)
        reconstruct(fixture, coefficients)
        for h in (2, 3, 6, 15):
            modified = [c + h * ((i % 3) - 1) for i, c in enumerate(coefficients)]
            reconstruct(fixture, modified, h)
        selected = max(fixture["projected"], key=lambda x: len(x["components"]))
        choices = [selected, fixture["flow_templates"][0]]
        for j, inner in enumerate(choices):
            highest = max(abs(x) for point in inner["values"] for x in point)
            alphabet = tuple(highest + 1 + i for i in range(d + 1))
            pattern = (1,) + tuple(-1 if (i + j) % 2 else 1 for i in range(1, d))
            outer = reflected_unit_selector(pattern, alphabet)
            check_compound_signature(outer, inner)
            signature_cases += 1
            # The largest d=4 compound is checked algebraically above; retain
            # the two-piece d=4 physical case to keep this control lightweight.
            if d < 4 or j == 1:
                certificate = physical_compound(outer, inner)
                physical_pairs.append({"dimension": 2 * d, "pairs": len(certificate["pairs"]),
                                       "components": len(inner["components"])})
                last_certificate = certificate
        fixture_reports.append({
            "inner_dimension": d,
            "raw_products": len(fixture["raw"]),
            "markers": len(fixture["markers"]),
            "projected_templates": len(fixture["projected"]),
            "marker_path_templates": len(fixture["flow_templates"]),
            "maximum_point_load": fixture["max_point_load"],
            "certified_fixture_point_load_bound": fixture["point_load_bound"],
            "maximum_routed_path_degree": fixture["max_path_degree"],
            "maximum_projected_piece_count": len(selected["components"]),
            "integer_and_composite_residue_reconstructions": 5,
        })

    # Shared-trace stages change exactly their two complementary families.
    shared_cases = 0
    for d in (2, 3, 4):
        left = reflected_unit_selector((1,) * d, tuple(range(1, d + 2)))
        right = reflected_unit_selector((1,) + (-1,) * (d - 1), tuple(range(d + 2, 2 * d + 3)))
        image = formula_signature(left + right)
        permitted = {tuple(range(d)), tuple(range(d, 2 * d))}
        require(all(len(line[0]) != 1 and
                    (len(line[0]) < d or line[0] in permitted) for line in image),
                "shared trace preservation")
        for native in permitted:
            require(any(line[0] == native for line in image), "missing complementary image")
        shared_cases += 1

    # Body-kernel membership does not imply vanishing proper contractions.
    inner = tensor(((1, 2), (1, 3), (4, 5)))
    check_body_kernel(inner, 3)
    image = sparse_signature(inner, 3)
    require(any(len(line[0]) == 2 for line in image), "missing lower-family counterexample")

    negatives = 0
    bad = deepcopy(last_certificate)
    bad["kind"] = "full-prime-arrangement"
    expect_rejection(lambda: verify_physical_compound(bad)); negatives += 1
    bad = deepcopy(last_certificate)
    points = list(bad["before"])
    bad["before"][points[1]] = bad["before"][points[0]]
    expect_rejection(lambda: verify_physical_compound(bad)); negatives += 1
    bad = deepcopy(last_certificate)
    bad["gap"] += 2
    expect_rejection(lambda: verify_physical_compound(bad)); negatives += 1
    bad = deepcopy(last_certificate)
    bad["pairs"].append(bad["pairs"][0])
    expect_rejection(lambda: verify_physical_compound(bad)); negatives += 1
    bad = deepcopy(last_certificate)
    bad["pairs"].pop()
    expect_rejection(lambda: verify_physical_compound(bad)); negatives += 1
    duplicate = [(1, ((1, 2), (1, 3))), (-1, ((1, 2), (1, 3)))]
    expect_rejection(lambda: component_sum(duplicate)); negatives += 1
    expect_rejection(lambda: check_body_kernel(tensor(((1, 2), (1, 3))), 2)); negatives += 1

    depths = {}
    for k in (4, 6, 8, 10, 12):
        levels = (2 * k - 3) + (k // 2) + 2
        last = (5 * k // 2) - 2
        require(levels == last + 1, "wrong even-dimensional correction depth")
        identities = comb(k, k // 2) * 2 ** (k - 2) // 2
        require(identities > 0, "shared trace count")
        depths[str(k)] = {"levels": levels, "last_index": last,
                          "shared_trace_identities": identities}
    report.update({"fixtures": fixture_reports, "complete_compound_signature_cases": signature_cases,
                   "actual_partial_prime_compounds": physical_pairs,
                   "shared_trace_signature_cases": shared_cases,
                   "proper_contraction_scope_counterexamples": 1,
                   "rejected_corruptions": negatives, "symbolic_even_depth_checks": depths})
    return report


if __name__ == "__main__":
    print(json.dumps(run_checks(), sort_keys=True, indent=2))
