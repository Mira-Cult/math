#!/usr/bin/env python3
"""Exact finite rank-two cuboid fixture; NOT an all-prime-line array.

Generate: python -B vector_trade_fixture.py generate --ring gaussian --output FILE
Verify:   python -B vector_trade_fixture.py verify FILE [FILE ...] --negative-controls

Two disjoint eight-cell cuboids act on one native body line. Each contains
four disjoint actual equal-gap pairs from the entire prescribed canonical
pool. Every other cell receives an unused pool element deterministically.
All four joint orientations are checked against all signed-coordinate lines.
The checker reconstructs its pool using check_certificate.pool_from_norms,
independently of the producer's prime_arrays.canonical_pool.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import itertools
import json
import math
from pathlib import Path

import check_certificate as independent

FORMAT = "quadratic-vector-trade-fixture-v1"
LABEL = "finite-physical-trade-fixture-not-an-all-prime-line-array"
FILLER = "unused-canonical-pool-in-order-to-unreserved-lexicographic-cells"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def coefficients(value):
    require(isinstance(value, list) and len(value) == 2 and
            all(type(x) is int for x in value), "invalid ring coordinates")
    return tuple(value)


def cell(value, n):
    require(isinstance(value, list) and len(value) == 3 and
            all(type(x) is int and 0 <= x < n for x in value), "invalid cell")
    return tuple(value)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def subtract(a, b):
    return a[0] - b[0], a[1] - b[1]


def index(c, n):
    return (c[0]*n + c[1])*n + c[2]


def digest(value):
    return hashlib.sha256(json.dumps(value, separators=(",", ":")).encode()).hexdigest()


def seed_pairs(pool, gap, occupied):
    """Choose four actual pairs greedily, without reusing any endpoint."""
    available = set(pool)
    used = set(occupied)
    selected = []
    for p in pool:
        q = add(p, gap)
        if p in used or q in used or q not in available or p == q:
            continue
        selected.append((p, q))
        used.update((p, q))
        if len(selected) == 4:
            return selected
    return None


def support_pairs(levels):
    """Pair along axis zero; positive tensor sign receives the lower prime."""
    result = []
    for r, s in itertools.product((0, 1), repeat=2):
        first = (levels[0][0], levels[1][r], levels[2][s])
        second = (levels[0][1], levels[1][r], levels[2][s])
        result.append((first, second) if (r+s) % 2 == 0 else (second, first))
    return result


def line_catalog(n):
    """Separate axis/face/body construction for predicted incidence effects."""
    catalog = {}
    def insert(coords, descriptor):
        key = tuple(sorted(index(c, n) for c in coords))
        require(key not in catalog, "duplicate catalog line")
        catalog[key] = descriptor
    for varying in range(3):
        fixed = [d for d in range(3) if d != varying]
        for values in itertools.product(range(n), repeat=2):
            coords = []
            for t in range(n):
                c = [0, 0, 0]
                c[varying] = t
                for d, value in zip(fixed, values):
                    c[d] = value
                coords.append(c)
            insert(coords, {"kind": "axis", "varying_axis": varying,
                            "fixed_coordinates": list(values)})
    for i, j in itertools.combinations(range(3), 2):
        fixed = next(d for d in range(3) if d not in (i, j))
        for sign in (1, -1):
            for value in range(n):
                coords = []
                for t in range(n):
                    c = [0, 0, 0]
                    c[i], c[j], c[fixed] = t, (t if sign == 1 else n-1-t), value
                    coords.append(c)
                insert(coords, {"kind": "face", "varying_axes": [i, j], "sign": sign,
                                "fixed_axis": fixed, "fixed_coordinate": value})
    for second, third in itertools.product((1, -1), repeat=2):
        insert([(t, t if second == 1 else n-1-t, t if third == 1 else n-1-t)
                for t in range(n)], {"kind": "body", "signs": [1, second, third]})
    return catalog


def predicted_change(descriptor, stages, bits):
    """Independent closed formula for the alternating cuboid's line action."""
    if descriptor["kind"] == "axis":
        return 0, 0
    total = (0, 0)
    for stage, active in zip(stages, bits):
        if not active:
            continue
        coefficient = 0
        if descriptor["kind"] == "body":
            coefficient = int(descriptor["signs"] == [1, 1, 1])
        elif descriptor["sign"] == 1:
            axis = descriptor["fixed_axis"]
            fixed = descriptor["fixed_coordinate"]
            a, other = stage["levels"][axis]
            coefficient = int(fixed == a) - int(fixed == other)
        gap = coefficients(stage["gap"])
        total = add(total, (coefficient*gap[0], coefficient*gap[1]))
    return total


def place(pool, stages, bits, n):
    array = [None] * len(pool)
    used = set()
    for stage, orientation in zip(stages, bits):
        for pair in stage["pairs"]:
            p, q = coefficients(pair["lower"]), coefficients(pair["upper"])
            positive, negative = cell(pair["positive_cell"], n), cell(pair["negative_cell"], n)
            left, right = (q, p) if orientation else (p, q)
            for location, value in ((positive, left), (negative, right)):
                j = index(location, n)
                require(array[j] is None and value not in used, "overlapping physical assignment")
                array[j] = value
                used.add(value)
    remaining = iter(z for z in pool if z not in used)
    for j in range(len(array)):
        if array[j] is None:
            array[j] = next(remaining)
    require(next(remaining, None) is None, "filler surplus")
    require(sorted(array) == sorted(pool), "physical state is not an exact pool permutation")
    return array


def line_sums(array, lines):
    return [tuple(sum(array[j][d] for j in line) for d in (0, 1)) for line in lines]


def pattern_records(pool, stages, n):
    lines = independent.geometric_lines(n, 3)
    catalog = line_catalog(n)
    require(sorted(catalog) == lines and len(lines) == 3*n*n+6*n+4, "incomplete signed-line catalog")
    native = tuple(index((t, t, t), n) for t in range(n))
    native_position = lines.index(native)
    baseline = place(pool, stages, [0, 0], n)
    baseline_sums = line_sums(baseline, lines)
    exact_total = tuple(sum(z[d] for z in pool) for d in (0, 1))
    records = []
    for mask in range(4):
        bits = [(mask >> j) & 1 for j in range(2)]
        array = place(pool, stages, bits, n)
        sums = line_sums(array, lines)
        actual_total = tuple(sum(z[d] for z in array) for d in (0, 1))
        require(actual_total == exact_total, "changed total pool sum")
        faces = []
        changed_axes = changed_other_bodies = changed_lines = 0
        for line, current, initial in zip(lines, sums, baseline_sums):
            delta = subtract(current, initial)
            description = catalog[line]
            require(delta == predicted_change(description, stages, bits), "wrong physical line action")
            if delta != (0, 0):
                changed_lines += 1
                if description["kind"] == "axis":
                    changed_axes += 1
                elif description["kind"] == "body" and line != native:
                    changed_other_bodies += 1
                elif description["kind"] == "face":
                    faces.append({"line": description, "change": list(delta), "sum": list(current)})
        require(changed_axes == changed_other_bodies == 0, "protected lines changed")
        records.append({"bits": bits, "native_sum": list(sums[native_position]),
                        "native_change": list(subtract(sums[native_position], baseline_sums[native_position])),
                        "face_changes": faces, "changed_axis_lines": changed_axes,
                        "changed_other_body_lines": changed_other_bodies,
                        "changed_signed_lines": changed_lines, "total_sum": list(actual_total),
                        "array_sha256": digest(array), "all_line_sums_sha256": digest(sums)})
    return records


def lattice_record(stages):
    a, b = (coefficients(stage["gap"]) for stage in stages)
    determinant = a[0]*b[1] - a[1]*b[0]
    require(determinant != 0, "rank-one gaps do not supply vector control")
    first = math.gcd(*a, *b)
    return {"basis_columns": [list(a), list(b)], "index": abs(determinant),
            "smith_invariants": [first, abs(determinant)//first]}


def boundary_record(extended_pool, ring):
    pool = extended_pool[:-1]
    return {"last": list(pool[-1]), "last_norm": independent.sqnorm(pool[-1], ring),
            "next": list(extended_pool[-1]), "next_norm": independent.sqnorm(extended_pool[-1], ring),
            "pool_sha256": digest(pool)}


def generate(ring, n=19):
    from prime_arrays import canonical_pool, primality_record
    require(ring in ("gaussian", "eisenstein"), "wrong ring")
    require(type(n) is int and n >= 17 and n % 2 == 1, "need eight noncentral reflection orbits")
    extended = canonical_pool(ring, n**3+1)
    pool = extended[:-1]
    occupied, stages = set(), []
    for j, preferred in enumerate(((2, 0), (0, 2))):
        candidates = [preferred] + sorted((a, b) for a in range(-6, 7) for b in range(-6, 7)
                                          if (a, b) != (0, 0) and (a, b) != preferred)
        selected = None
        for gap in candidates:
            if stages:
                first = stages[0]["gap"]
                if first[0]*gap[1] == first[1]*gap[0]:
                    continue
            selected = seed_pairs(pool, gap, occupied)
            if selected is not None:
                break
        require(selected is not None, "no independent four-pair supply in the finite search")
        a = 4*j
        levels = [[a, a+1], [a, a+2], [a, a+3]]
        pairs = []
        for (p, q), (positive, negative) in zip(selected, support_pairs(levels)):
            pairs.append({"lower": list(p), "upper": list(q),
                          "lower_primality": primality_record(p, ring),
                          "upper_primality": primality_record(q, ring),
                          "positive_cell": list(positive), "negative_cell": list(negative)})
            occupied.update((p, q))
        stages.append({"gap": list(gap), "levels": levels, "pairs": pairs})
    return {"format": FORMAT, "label": LABEL, "ring": ring, "n": n,
            "dimension": 3, "family": "full-signed-coordinate-lines", "pool_count": n**3,
            "pool_boundary": boundary_record(extended, ring), "coordinates": "lexicographic-zero-based",
            "filler_rule": FILLER, "native_body": [1, 1, 1], "stages": stages,
            "increment_lattice": lattice_record(stages), "patterns": pattern_records(pool, stages, n),
            "scope": {"all_prime_line_sums_claimed": False, "asymptotic_construction_claimed": False,
                      "claim": "two actual independent cuboid increments on one exact pool permutation"}}


def verify(obj):
    require(obj.get("format") == FORMAT and obj.get("label") == LABEL, "wrong fixture format or label")
    ring, n = obj.get("ring"), obj.get("n")
    require(ring in ("gaussian", "eisenstein"), "wrong ring")
    require(type(n) is int and n >= 17 and n % 2 == 1, "wrong cube order")
    require(obj.get("dimension") == 3 and obj.get("pool_count") == n**3, "wrong pool shape")
    require(obj.get("family") == "full-signed-coordinate-lines", "wrong family")
    require(obj.get("coordinates") == "lexicographic-zero-based" and obj.get("filler_rule") == FILLER,
            "unsupported coordinates or filler")
    require(obj.get("native_body") == [1, 1, 1], "wrong native body")
    scope = obj.get("scope", {})
    require(scope.get("all_prime_line_sums_claimed") is False and
            scope.get("asymptotic_construction_claimed") is False, "fixture exceeds its proof scope")
    extended = independent.pool_from_norms(ring, n**3+1)
    pool, pool_set = extended[:-1], set(extended[:-1])
    require(obj.get("pool_boundary") == boundary_record(extended, ring), "wrong canonical cutoff or tie")
    stages = obj.get("stages")
    require(isinstance(stages, list) and len(stages) == 2, "need exactly two stages")
    used_primes, used_cells, used_orbits = set(), set(), set()
    for stage in stages:
        gap = coefficients(stage["gap"])
        require(gap != (0, 0), "zero gap")
        levels = stage["levels"]
        require(isinstance(levels, list) and len(levels) == 3 and
                all(isinstance(p, list) and len(p) == 2 and
                    all(type(x) is int and 0 <= x < n for x in p) for p in levels), "bad levels")
        a = levels[0][0]
        require(all(p[0] == a for p in levels), "native coordinates must agree")
        base_values = [a] + [p[1] for p in levels]
        orbits = [min(x, n-1-x) for x in base_values]
        require(len(set(orbits)) == 4 and (n-1)//2 not in orbits and
                not (set(orbits) & used_orbits), "reflection orbits overlap or hit the center")
        used_orbits.update(orbits)
        pairs = stage["pairs"]
        require(isinstance(pairs, list) and len(pairs) == 4, "a cuboid needs four actual pairs")
        for pair, expected in zip(pairs, support_pairs(levels)):
            p, q = coefficients(pair["lower"]), coefficients(pair["upper"])
            require(p in pool_set and q in pool_set and subtract(q, p) == gap, "pair is not an actual common-gap pool pair")
            require(p != q and p not in used_primes and q not in used_primes, "reused prime endpoint")
            require(pair["lower_primality"] == independent.classified(p, ring) and
                    pair["upper_primality"] == independent.classified(q, ring), "false endpoint primality")
            used_primes.update((p, q))
            positive, negative = cell(pair["positive_cell"], n), cell(pair["negative_cell"], n)
            require((positive, negative) == expected, "wrong alternating cuboid support")
            require(positive not in used_cells and negative not in used_cells, "reused support cell")
            used_cells.update((positive, negative))
    lattice = lattice_record(stages)
    require(obj.get("increment_lattice") == lattice, "wrong increment lattice")
    records = pattern_records(pool, stages, n)
    require(obj.get("patterns") == records, "wrong vector action, face drift, or physical-state digest")
    require(len({tuple(p["native_change"]) for p in records}) == 4, "native changes are not four distinct vectors")
    return {"ring": ring, "n": n, "entries": len(pool), "lines": 3*n*n+6*n+4,
            "orientations": len(records), "actual_pairs": len(used_primes)//2,
            "reserved_cells": len(used_cells), "gaps": [s["gap"] for s in stages],
            "lattice_index": lattice["index"], "native_changes": [r["native_change"] for r in records],
            "all_prime_line_array": False, "asymptotic_construction": False}


def negative_controls(obj):
    mutants = []
    def mutate(label, operation):
        candidate = copy.deepcopy(obj)
        operation(candidate)
        mutants.append((label, candidate))
    def reuse_endpoint(x):
        first, second = x["stages"][0]["pairs"][:2]
        for key in ("lower", "upper", "lower_primality", "upper_primality"):
            second[key] = copy.deepcopy(first[key])
    def rotate_endpoint(x):
        a, b = x["stages"][0]["pairs"][0]["lower"]
        x["stages"][0]["pairs"][0]["lower"] = [-b, a] if x["ring"] == "gaussian" else [a-b, a]
    mutate("reused actual pair", reuse_endpoint)
    mutate("corrupt support", lambda x: x["stages"][0]["pairs"][0]["positive_cell"].__setitem__(0, 8))
    mutate("corrupt gap", lambda x: x["stages"][0]["gap"].__setitem__(0, x["stages"][0]["gap"][0]+1))
    mutate("missing fourth pair", lambda x: x["stages"][0]["pairs"].pop())
    mutate("individual unit rotation", rotate_endpoint)
    mutate("false second coordinate action", lambda x: x["patterns"][3]["native_change"].__setitem__(1, 999))
    mutate("false face drift", lambda x: x["patterns"][1]["face_changes"][0]["change"].__setitem__(0, 999))
    mutate("wrong cutoff tie", lambda x: x["pool_boundary"].__setitem__("last", x["pool_boundary"]["next"]))
    mutate("wrong filler rule", lambda x: x.__setitem__("filler_rule", "arbitrary replacements"))
    mutate("unjustified prime-array label", lambda x: x["scope"].__setitem__("all_prime_line_sums_claimed", True))
    for label, candidate in mutants:
        try:
            verify(candidate)
        except (ValueError, KeyError, TypeError):
            continue
        raise AssertionError("corrupt fixture accepted: " + label)
    return [label for label, _ in mutants]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    gen = commands.add_parser("generate")
    gen.add_argument("--ring", choices=("gaussian", "eisenstein"), required=True)
    gen.add_argument("--n", type=int, default=19)
    gen.add_argument("--output", type=Path, required=True)
    check = commands.add_parser("verify")
    check.add_argument("files", type=Path, nargs="+")
    check.add_argument("--negative-controls", action="store_true")
    args = parser.parse_args()
    if args.command == "generate":
        obj = generate(args.ring, args.n)
        result = verify(obj)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(obj, indent=2)+"\n")
        print(json.dumps({"status": "generated-and-verified-fixture", "output": str(args.output), **result}))
    else:
        for path in args.files:
            obj = json.loads(path.read_text())
            result = verify(obj)
            if args.negative_controls:
                result["rejected_mutations"] = negative_controls(obj)
            print(json.dumps({"status": "verified-fixture", "file": str(path), **result}))


if __name__ == "__main__":
    main()
