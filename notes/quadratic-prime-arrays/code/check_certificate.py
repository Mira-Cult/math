#!/usr/bin/env python3
"""Independent exact checker: no import from the producer/search utilities.

Trial division checks every primality claim, including inert rational primes.
Pool enumeration is by norm, solving quadratic equations for coordinates;
line enumeration is by a varying-coordinate subset and normalized signs.
"""
from __future__ import annotations

import argparse
import copy
import itertools
import json
import math
from pathlib import Path


def is_prime(k):
    if type(k) is not int or k < 2:
        return False
    for divisor in range(2, math.isqrt(k) + 1):
        if k % divisor == 0:
            return False
    return True


def sqnorm(pair, ring):
    x, y = pair
    return x*x + y*y - (x*y if ring == "eisenstein" else 0)


def classified(pair, ring):
    a, b = pair
    value = sqnorm(pair, ring)
    if is_prime(value):
        return {"kind": "rational-prime-norm", "rational_prime": value,
                "trial_division_through": math.isqrt(value)}
    p = math.isqrt(value)
    on_unit_ray = (a == 0 or b == 0) if ring == "gaussian" else (a == 0 or b == 0 or a == b)
    residue, modulus = (3, 4) if ring == "gaussian" else (2, 3)
    if value == p*p and on_unit_ray and is_prime(p) and p % modulus == residue:
        return {"kind": "inert-rational-associate", "rational_prime": p,
                "trial_division_through": math.isqrt(p)}
    return None


def pool_from_norms(ring, length):
    result = []
    q = 2
    while len(result) < length:
        if q == (2 if ring == "gaussian" else 3):
            q += 1
            continue
        shell = []
        if is_prime(q):
            for a in range(1, 2 * math.isqrt(q) + 2):
                if ring == "gaussian":
                    v = q - a*a
                    if v >= 0:
                        b = math.isqrt(v)
                        if b*b == v:
                            shell.append((a, b))
                else:
                    disc = 4*q - 3*a*a
                    if disc < 0:
                        continue
                    root = math.isqrt(disc)
                    if root*root != disc:
                        continue
                    for sign in (-1, 1):
                        twice_b = a + sign*root
                        if twice_b % 2 == 0:
                            b = twice_b // 2
                            if a > b >= 0:
                                shell.append((a, b))
        p = math.isqrt(q)
        residue, modulus = (3, 4) if ring == "gaussian" else (2, 3)
        if p*p == q and is_prime(p) and p % modulus == residue:
            shell.append((p, 0))
        result.extend(sorted(set(shell)))
        q += 1
    return result[:length]


def geometric_lines(n, dimension):
    all_lines = set()
    for r in range(1, dimension + 1):
        for active in itertools.combinations(range(dimension), r):
            fixed = [d for d in range(dimension) if d not in active]
            for later_signs in itertools.product((1, -1), repeat=r-1):
                signs = (1,) + later_signs
                for constants in itertools.product(range(n), repeat=len(fixed)):
                    subset = []
                    for t in range(n):
                        c = [0] * dimension
                        for d, value in zip(fixed, constants):
                            c[d] = value
                        for d, sign in zip(active, signs):
                            c[d] = t if sign == 1 else n-1-t
                        index = 0
                        for value in c:
                            index = index*n + value
                        subset.append(index)
                    all_lines.add(tuple(sorted(subset)))
    return sorted(all_lines)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def coordinate(value):
    require(isinstance(value, list) and len(value) == 2 and all(type(x) is int for x in value),
            "invalid coefficient pair")
    return tuple(value)


def verify(obj):
    require(obj.get("format") == "quadratic-prime-array-v1", "wrong format")
    ring = obj.get("ring")
    n, dimension = obj.get("n"), obj.get("dimension")
    require(ring in ("gaussian", "eisenstein"), "wrong ring")
    require(type(n) is int and n >= 1 and type(dimension) is int and dimension in (2, 3), "wrong shape")
    require(obj.get("family") == "full-signed-coordinate-lines", "wrong line family")
    expected_coords = list(map(list, itertools.product(range(n), repeat=dimension)))
    require(obj.get("coordinates") == expected_coords, "wrong cell coordinate order")
    length = n ** dimension
    pool = pool_from_norms(ring, length)
    actual_pool = list(map(coordinate, obj["pool"]))
    array = list(map(coordinate, obj["array"]))
    require(actual_pool == pool, "not the prescribed norm-ordered pool")
    require(len(array) == length and sorted(array) == sorted(pool), "not a bijection of the pool")
    require(len(obj["entry_primality"]) == length, "missing entry primality")
    for z, record in zip(pool, obj["entry_primality"]):
        a, b = z
        require((a > 0 and b >= 0) if ring == "gaussian" else (a > b >= 0), "wrong canonical sector")
        classification = classified(z, ring)
        require(classification is not None and record == classification, "invalid entry primality record")
    expected_lines = geometric_lines(n, dimension)
    expected_count = 1 if n == 1 else (2*n+2 if dimension == 2 else 3*n*n+6*n+4)
    require(len(expected_lines) == expected_count, "line enumeration formula failed")
    require(len(obj["lines"]) == len(expected_lines), "missing/extra line")
    for expected, record in zip(expected_lines, obj["lines"]):
        require(record["cells"] == list(expected), "wrong or unsorted geometric line")
        actual_sum = tuple(sum(array[j][d] for j in expected) for d in (0, 1))
        require(coordinate(record["sum"]) == actual_sum, "wrong line sum")
        require(record["norm"] == sqnorm(actual_sum, ring), "wrong line norm")
        classification = classified(actual_sum, ring)
        require(classification is not None and record["primality"] == classification,
                "line sum is not a certified prime element")
    return {"ring": ring, "n": n, "dimension": dimension, "entries": length,
            "lines": len(expected_lines), "inert_entries": sum(z[1] == 0 for z in pool),
            "inert_line_sums": sum(r["primality"]["kind"] == "inert-rational-associate" for r in obj["lines"])}


def verify_obstruction(obj):
    require(obj.get("format") == "quadratic-prime-obstruction-v1", "wrong obstruction format")
    require(obj.get("ring") == "eisenstein" and obj.get("residue_ideal") == "1-omega", "wrong ring/ideal")
    n, dimension = obj.get("n"), obj.get("dimension")
    require(type(n) is int and n >= 2 and type(dimension) is int and dimension in (2, 3), "wrong obstruction shape")
    require(obj.get("family") == "full-signed-coordinate-lines", "wrong family")
    pool = pool_from_norms("eisenstein", n ** dimension)
    require(list(map(coordinate, obj["pool"])) == pool, "wrong obstruction pool")
    residues = [(a+b) % 3 for a, b in pool]
    require(all(r in (1, 2) for r in residues), "ramified input")
    plus = residues.count(1)
    require(obj.get("plus_count") == plus and obj.get("minus_count") == len(pool)-plus, "wrong residue count")
    require(type(obj.get("uses_total_count")) is bool, "invalid total-count flag")
    # Re(a+b*omega)=(2a-b)/2. Every n-entry sum exceeds the norm-3 exception.
    require((n * min(2*a-b for a, b in pool))**2 > 12, "small ramified associate exception not excluded")
    lines = geometric_lines(n, dimension)
    require(len(lines) == (2*n+2 if dimension == 2 else 3*n*n+6*n+4), "obstruction line count failed")
    allowed = [j for j in range(n+1) if (2*j-n) % 3 != 0]
    require(obj.get("allowed_line_plus_counts") == allowed, "wrong line congruence")
    counts = {"nodes": 0, "leaves": 0, "forced_assignments": 0}
    def data_for(reason, assignment):
        if set(reason) == {"line"}:
            k = reason["line"]
            require(type(k) is int and 0 <= k < len(lines), "invalid reason line")
            cells, choices = lines[k], allowed
        else:
            require(reason == {"total": True} and obj["uses_total_count"], "invalid total-count reason")
            cells, choices = tuple(range(len(pool))), [plus]
        count = sum(assignment[j] == 1 for j in cells)
        unknown = [j for j in cells if assignment[j] == -1]
        possible = [k for k in choices if count <= k <= count+len(unknown)]
        return cells, count, unknown, possible
    def consume(node, assignment):
        counts["nodes"] += 1
        for instruction in node["forced"]:
            j, value = instruction["cell"], instruction["value"]
            require(type(j) is int and 0 <= j < len(pool) and assignment[j] == -1, "invalid forced cell")
            require(type(value) is int and value in (0, 1), "invalid forced value")
            cells, count, unknown, possible = data_for(instruction["reason"], assignment)
            require(j in cells and possible, "invalid forced reason")
            require(possible == ([count] if value == 0 else [count+len(unknown)]), "unjustified propagation")
            assignment[j] = value
            counts["forced_assignments"] += 1
        if "contradiction" in node:
            require(set(node) == {"forced", "contradiction"}, "ambiguous proof node")
            require(not data_for(node["contradiction"], assignment)[3], "false contradiction")
            counts["leaves"] += 1
            return
        require(set(node) == {"forced", "branch_cell", "children"}, "invalid branching node")
        j = node["branch_cell"]
        require(type(j) is int and 0 <= j < len(pool) and assignment[j] == -1, "invalid branch cell")
        require(len(node["children"]) == 2, "branch must cover both residues")
        for value, child in enumerate(node["children"]):
            next_assignment = assignment.copy()
            next_assignment[j] = value
            consume(child, next_assignment)
    consume(obj["proof"], [-1] * len(pool))
    require(counts["nodes"] == obj.get("producer_node_count"), "wrong proof count")
    return {"ring": "eisenstein", "n": n, "dimension": dimension, "entries": len(pool),
            "lines": len(lines), "plus_count": plus, "minus_count": len(pool)-plus,
            "uses_total_count": obj["uses_total_count"], **counts}


def obstruction_negative_controls(obj):
    mutated = []
    for key, value in (("plus_count", obj["plus_count"]+1), ("allowed_line_plus_counts", list(range(obj["n"]+1)))):
        copy_obj = copy.deepcopy(obj)
        copy_obj[key] = value
        mutated.append(copy_obj)
    copy_obj = copy.deepcopy(obj)
    copy_obj["proof"] = {"forced": [], "contradiction": {"line": 0}}
    mutated.append(copy_obj)
    copy_obj = copy.deepcopy(obj)
    copy_obj["proof"]["children"].pop()
    mutated.append(copy_obj)
    for altered in mutated:
        try:
            verify_obstruction(altered)
        except (ValueError, KeyError, TypeError):
            continue
        raise AssertionError("invalid obstruction accepted")
    return len(mutated)


def negative_controls(obj):
    mutations = []
    def changed(label, operation):
        altered = copy.deepcopy(obj)
        operation(altered)
        mutations.append((label, altered))
    changed("omitted line", lambda x: x["lines"].pop())
    changed("false sum", lambda x: x["lines"][0]["sum"].__setitem__(0, x["lines"][0]["sum"][0]+1))
    changed("false norm", lambda x: x["lines"][0].__setitem__("norm", x["lines"][0]["norm"]+1))
    changed("false primality witness", lambda x: x["entry_primality"][0].__setitem__("rational_prime", 4))
    changed("wrong coordinates", lambda x: x["coordinates"][0].__setitem__(0, -1))
    changed("rotated representative", lambda x: x["array"][0].__setitem__(0, -x["array"][0][0]))
    if len(obj["array"]) > 1:
        changed("duplicate entry", lambda x: x["array"].__setitem__(1, x["array"][0]))
        changed("pool reordered", lambda x: x["pool"].__setitem__(slice(0, 2), list(reversed(x["pool"][:2]))))
    for label, altered in mutations:
        try:
            verify(altered)
        except (ValueError, KeyError, TypeError):
            continue
        raise AssertionError("negative control accepted: " + label)
    return len(mutations)


def arithmetic_controls():
    # Units, inert associates on several unit rays, and ramified primes.
    examples = [("gaussian", (3, 0), True), ("gaussian", (0, -3), True),
                ("gaussian", (1, 1), True), ("gaussian", (5, 0), False),
                ("gaussian", (1, 0), False), ("gaussian", (2, 2), False),
                ("eisenstein", (2, 0), True), ("eisenstein", (0, -2), True),
                ("eisenstein", (-2, -2), True), ("eisenstein", (1, -1), True),
                ("eisenstein", (7, 0), False), ("eisenstein", (1, 1), False)]
    for ring, z, answer in examples:
        require((classified(z, ring) is not None) == answer, "arithmetic control failed")
    require(pool_from_norms("gaussian", 3) == [(1, 2), (2, 1), (3, 0)], "Gaussian boundary convention failed")
    require(pool_from_norms("eisenstein", 3) == [(2, 0), (3, 1), (3, 2)], "Eisenstein boundary convention failed")
    return len(examples)+2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="+", type=Path)
    parser.add_argument("--negative-controls", action="store_true")
    args = parser.parse_args()
    arithmetic_controls()
    for path in args.files:
        obj = json.loads(path.read_text())
        if obj.get("format") == "quadratic-prime-obstruction-v1":
            result = verify_obstruction(obj)
            if args.negative_controls:
                result["rejected_mutations"] = obstruction_negative_controls(obj)
        else:
            result = verify(obj)
            if args.negative_controls:
                result["rejected_mutations"] = negative_controls(obj)
        print(json.dumps({"file": str(path), "status": "verified", **result}, sort_keys=True))


if __name__ == "__main__":
    main()
