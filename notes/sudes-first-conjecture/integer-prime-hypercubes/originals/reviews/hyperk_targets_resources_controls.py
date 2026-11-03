#!/usr/bin/env python3
"""Reviewer controls bound to scientific revision 5692d376.

Independent arithmetic, geometric target, grid and centering diagnostics.
No asymptotic prime-distribution or array-existence certificate is produced.
Usage: python3 -B this_file.py PATH_TO_ARCHIVE_OF_FROZEN_REPOSITORY
"""
from __future__ import annotations

from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import reduce
from itertools import permutations, product
from math import gcd, isqrt
from pathlib import Path
import argparse
import copy
import hashlib
import importlib.util
import json
import random


REVISION = "5692d37633ef4b509e8429cddf4ed762e7235d08"
PREFIX = Path("problems/prime-arrays-beyond-square")
HASHES = {
    "manuscripts/hyperk_targets.md": "2a69a31ce1a3ecde164bf7748dc52c22b2637551bc97dd821edd497ea9df5306",
    "manuscripts/hyperk_resources.md": "c26bd5d67dd3dee746c986c1d11695a4ba92d2aeda53f0e5441b1adf113ce0a7",
    "manuscripts/cube_targets.md": "b92be738cd42c0ec61c6ed40004c267ce631ba08dc37899656cd1055f8388559",
    "code/hyperk_targets.py": "6fa292732db53e6ce17a388fdd34dfd5cc476e858887fb6c3df2a699335cfb9f",
    "code/hyperk_resources.py": "4c17e6cbbd1e3a2cd0a1f89057ccf283870222deea82ab3ee0554b3804bac2e7",
    "inputs/hyperk-targets-k5-n5.json": "00c4d69d5b71e128ac059d47e46041bf96c927e8346af77ab0c6ae0542cff649",
    "inputs/hyperk-targets-k6-n5.json": "95bb9ea3c025eb0e5e852b7fc8d9cc576feb75bb3694a4cf531bd3090ac16ec6",
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def reject(fn):
    try:
        fn()
    except (ValueError, KeyError, TypeError):
        return
    raise AssertionError("corruption was accepted")


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def bind_sources(root):
    for relative, expected in HASHES.items():
        actual = hashlib.sha256((root / PREFIX / relative).read_bytes()).hexdigest()
        need(actual == expected, "wrong frozen source: " + relative)


def weight_controls(author):
    # Occupancy-state recurrence, without inclusion-exclusion or Stirling numbers.
    checked = 0
    for m in range(1, 6):
        counts = {frozenset(): 1}
        for r in range(1, 13):
            following = defaultdict(int)
            for labels, value in counts.items():
                for label in range(m + 1):
                    following[labels | {label}] += value * (1 if label == 0 else 2)
            counts = following
            assert sum(counts.values()) == (2 * m + 1) ** r
            for labels, actual in counts.items():
                assert actual == author.label_weight(r, tuple(sorted(labels)))
                checked += 1

    # A separate last-coordinate recurrence verifies all weights and their gcd.
    # w[r,s] counts a prescribed positive-label set; v[r,s] also requires zero.
    old_w, old_v = [1], [0]
    for r in range(1, 129):
        def at(row, s):
            return row[s] if 0 <= s < len(row) else 0
        w = [2 * s * (at(old_w, s) + at(old_w, s - 1)) for s in range(r + 1)]
        v = [(1 + 2 * s) * at(old_v, s) + 2 * s * at(old_v, s - 1)
             + at(old_w, s) for s in range(r + 1)]
        assert v[0] == 1 and v[r] == 0
        for s in range(1, r + 1):
            assert w[s] == author.nozero_weight(r, s)
        for s in range(r):
            assert v[s] == author.zero_weight(r, s)
        d = reduce(gcd, w[1:] + v[1:r])
        assert d == author.reserve_gcd(r)
        assert d & (d - 1) == 0
        if r >= 2:
            assert d == gcd(w[1], v[1])
        assert max(w + v) <= (2 * r) ** r
        old_w, old_v = w, v
    return {"occupancy_weight_entries": checked, "recurrence_gcd_degrees": 128}


def completion_controls(author):
    rng = random.Random(8120261102)
    checked = 0
    for r in range(1, 65):
        a = 2 ** r
        b = 3 ** r - 2 ** r - 1 if r >= 2 else 0
        d = gcd(a, b)
        for j in range(25):
            m = rng.randrange(1, 50)
            mu = F(rng.randrange(1, 10 ** 10), rng.randrange(1, 1000))
            ideal = (a + b) * m * mu
            # Deliberately choose exact compatible totals on both sides of ideal.
            z = int((ideal - (a + b) * m) / (2 * d)) + j - 12
            residual = (a + b) * m + 2 * d * z
            totals = author.centered_finish(r, m, mu, residual)
            assert totals[0] % 2 == m % 2
            if r == 1:
                assert a * totals[0] == residual
            else:
                sa, sb = totals
                assert sb % 2 == m % 2
                assert a * sa + b * sb == residual
                assert abs(sb - m * mu) <= a // d
                assert abs(sa - m * mu) <= abs(residual - ideal) / a + b // d
            reject(lambda: author.centered_finish(r, m, mu, residual + 2))
            checked += 1
    # A residue modulo D is insufficient: 96=80 mod 16 but not mod 32.
    assert all((16 * a + 64 * b) % 32 == 16
               for a in range(-9, 10, 2) for b in range(-9, 10, 2))
    reject(lambda: author.centered_finish(4, 1, F(1), 96))
    # Greedy bulk discrepancy stays bounded independently of list length.
    discrepancy = F(0)
    mu, delta, limit = F(100003, 7), F(100, 3), 2 ** 20
    for j in range(10000):
        weight = 1 + (7919 * j) % limit
        prime_surrogate = mu - delta if discrepancy >= 0 else mu + delta / 2
        discrepancy += weight * (prime_surrogate - mu)
        assert abs(discrepancy) <= limit * delta
    return {"centered_completions": checked, "wrong_residues_rejected": checked + 1,
            "bulk_greedy_steps": 10000}


def prime(p):
    return type(p) is int and p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def first_odd_pool(size):
    result, candidate = [], 3
    while len(result) < size:
        if prime(candidate):
            result.append(candidate)
        candidate += 2
    return result


def independent_target_check(cert, geometric=True):
    need(cert["kind"] == "signed-line-prime-target-vector", "wrong certificate kind")
    k, n = cert["dimension"], cert["order"]
    need(type(k) is int and type(n) is int and k >= 2 and n >= 3 and n % 2,
         "invalid dimension or order")
    need(cert["pool"] == "exact-first-n^k-odd-primes", "wrong exact pool")
    need(cert["rule"] == "ordinary-set-of-absolute-fixed-labels; empty-uses-{0}", "wrong rule")
    total = sum(first_odd_pool(n ** k))
    need(total == cert["pool_total"], "wrong initial-prime total")
    q = {}
    for item in cert["q"]:
        labels = tuple(item["labels"])
        need(all(type(a) is int for a in labels), "nonintegral label")
        need(labels == tuple(sorted(set(labels))) and labels not in q, "bad label set")
        need(prime(item["prime"]) and item["prime"] > 2, "bad target prime")
        q[labels] = item["prime"]
    I = tuple(range(-(n // 2), n // 2 + 1))
    actual_labels = {tuple(sorted({abs(x) for x in point})) for point in product(I, repeat=k - 1)}
    need(set(q) == actual_labels, "missing or extraneous label set")
    need(sum(q[tuple(sorted({abs(x) for x in point}))] for point in product(I, repeat=k - 1))
         == total, "wrong directional total")
    den = n ** (k - 1)
    need(all(abs(p * den - total) ** 5 <= total ** 3 * den ** 2 for p in q.values()),
         "wrong target radius")
    need(cert["line_count"] == ((n + 2) ** k - n ** k) // 2, "wrong line count")
    if not geometric:
        return None

    # Build geometric lines using coordinate functions, with reversal removed.
    choices = [(0, c) for c in I] + [(1, 0), (-1, 0)]
    line_values = {}
    for funcs in product(choices, repeat=k):
        slopes = [s for s, _ in funcs if s]
        if not slopes or slopes[0] < 0:
            continue
        cells = frozenset(tuple(s * t + c for s, c in funcs) for t in I)
        label = tuple(sorted({abs(c) for s, c in funcs if s == 0})) or (0,)
        need(cells not in line_values, "duplicate geometric line")
        line_values[cells] = q[label]
    need(len(line_values) == cert["line_count"], "geometry loses a line")

    # Independently split every geometric two-parameter section in both ways.
    choices2 = [(0, 0, c) for c in I] + [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0)]
    sections = 0
    for funcs in product(choices2, repeat=k):
        posa = [j for j, (a, b, c) in enumerate(funcs) if a]
        posb = [j for j, (a, b, c) in enumerate(funcs) if b]
        if not posa or not posb or posa[0] > posb[0]:
            continue
        if funcs[posa[0]][0] < 0 or funcs[posb[0]][1] < 0:
            continue
        rows, cols = [], []
        for t in I:
            rows.append(frozenset(tuple(a * s + b * t + c for a, b, c in funcs) for s in I))
            cols.append(frozenset(tuple(a * t + b * s + c for a, b, c in funcs) for s in I))
        need(sum(line_values[line] for line in rows) == sum(line_values[line] for line in cols),
             "broken geometric partition")
        sections += 1
    return {"k": k, "n": n, "exact_pool_total": total,
            "full_geometric_lines": len(line_values), "geometric_sections": sections,
            "integer_lift_checked": False, "arrangement_checked": False}


def fixture_controls(root):
    results, negative = [], 0
    for k in (5, 6):
        cert = json.loads((root / PREFIX / f"inputs/hyperk-targets-k{k}-n5.json").read_text())
        results.append(independent_target_check(cert))
        bad = []
        c = copy.deepcopy(cert); c["q"][0]["prime"] = 9; bad.append(c)
        c = copy.deepcopy(cert); c["q"].pop(); bad.append(c)
        c = copy.deepcopy(cert); c["q"].append(c["q"][0]); bad.append(c)
        c = copy.deepcopy(cert); c["pool_total"] += 2; bad.append(c)
        c = copy.deepcopy(cert); c["line_count"] -= 1; bad.append(c)
        c = copy.deepcopy(cert); c["kind"] = "prime-array-arrangement"; bad.append(c)
        c = copy.deepcopy(cert); c["rule"] = "multiset-of-labels"; bad.append(c)
        for c in bad:
            reject(lambda: independent_target_check(c, False))
            negative += 1
    return {"fixtures": results, "corruptions_rejected": negative}


def ladder_controls(author):
    cases = 0
    for k in range(2, 33):
        for depth in (0, 1, 2 * k - 4, 3 * k - k // 2 - 4, 3 ** k, 10 ** 6):
            a0 = F(3, 5)
            last = F(3, 4) - F(3, 20 * (depth + 1))
            assert last < F(3, 4)
            assert F(4, 5) - last > F(1, 20)
            assert a0 - last / 2 > F(9, 40)
            assert F(k) - F(3, 5) * (k + 1) > 0
            result = author.ledger(k, depth)
            assert F(result["last"]) == last
            for value in result["margins"].values():
                assert F(value) > 0
            cases += 1
    # Exact analytic power slack for the local counting import.
    assert F(71, 120) - F(7, 12) - F(1, 240) == F(1, 240)
    for endpoint in (F(4, 5), F(81, 100), F(1)):
        reject(lambda: author.reject_fixed_endpoint(endpoint))
    return {"fixed_dimension_depth_cases": cases, "bad_endpoints_rejected": 3,
            "diagnostics": [author.ledger(5, 9), author.ledger(6, 11)]}


def grid_controls():
    checked = 0
    for g in (2, 6, 30):
        for kcap in (1, 2, 5):
            X = 60 * g
            gaps = [g] * 60 + [15 * g + g * (i % 16) for i in range(32 * kcap)]
            reachable = {0: 0}
            for i, gap in enumerate(gaps):
                old = dict(reachable)
                for value, mask in old.items():
                    reachable.setdefault(value + gap, mask | (1 << i))
            R = sum(gaps)
            assert set(reachable) == set(range(0, R + 1, g))
            assert R >= 8 * kcap * X
            q = g * (R // (2 * g))
            mask = reachable[q]
            assert sum(gaps[i] for i in range(len(gaps)) if mask >> i & 1) == q
            assert abs(R - 2 * q) <= g
            for central in (q, R - q):
                assert all(central + change in reachable
                           for change in range(-3 * kcap * X, 3 * kcap * X + 1, g))
            checked += 1
    # A common gcd alone does not produce a complete interval of subset sums.
    bad = {0, 4, 6, 10}
    assert gcd(4, 6) == 2 and 2 not in bad and 8 not in bad

    # One actual difference multigraph check, with density and matching constants.
    # This is an arithmetic set, not an assertion about finite prime density.
    M, g, density_factor = 2, 2, 1
    R = 256 * (M + 1) * g * density_factor ** 2
    S = tuple(range(0, R, g))
    edges = defaultdict(list)
    for i, a in enumerate(S):
        for b in S[i + 1:]:
            if b - a >= F(R, 32 * density_factor):
                edges[b - a].append((a, b))
    d, pairs = max(edges.items(), key=lambda item: len(item[1]))
    assert len(pairs) >= F(R, 16 * g * density_factor ** 2)
    degree = Counter(x for pair in pairs for x in pair)
    assert max(degree.values()) <= 2
    used, matching = set(), []
    for pair in pairs:
        if not used.intersection(pair):
            matching.append(pair)
            used.update(pair)
    assert len(matching) >= M
    assert F(R, 32 * density_factor) <= d <= R and d % g == 0
    return {"complete_grid_cases": checked, "growth_matching_size": len(matching),
            "scope": "finite arithmetic mechanisms only; no prime density assertion"}


def centering_controls():
    # Two genuine prime pairs, whole complementary reference states, exact pool.
    pool = first_odd_pool(9)
    bar = F(sum(pool), 9)
    reference = [{(0, 0): 5, (0, 1): 17, (1, 0): 11, (1, 1): 7},
                 {(0, 0): 11, (0, 1): 7, (1, 0): 5, (1, 1): 17}]
    lines = [tuple((i, j) for i in range(3)) for j in range(3)]
    lines += [tuple((i, j) for j in range(3)) for i in range(3)]
    lines += [tuple((i, i) for i in range(3)), tuple((i, 2 - i) for i in range(3))]
    unoccupied = [cell for cell in product(range(3), repeat=2) if cell not in reference[0]]
    unused = [p for p in pool if p not in reference[0].values()]
    umean = F(sum(unused), len(unused))
    assert umean != bar  # Assuming the unused mean remains bar is false.
    residual_total = sum(reference[0].values()) - 4 * bar
    assert umean - bar == -residual_total / len(unused)
    completions = 0
    for fixed in reference:
        E = max(abs(sum(fixed.get(cell, 0) for cell in line)
                    - sum(cell in fixed for cell in line) * bar) for line in lines)
        assert abs(umean - bar) <= F(3, len(unused)) * E <= 2 * E / 3
        sums = [0] * len(lines)
        for ordered in permutations(unused):
            array = dict(fixed)
            array.update(zip(unoccupied, ordered))
            assert sorted(array.values()) == pool
            for j, line in enumerate(lines):
                sums[j] += sum(array[cell] for cell in line)
            completions += 1
        count = 120
        for j, line in enumerate(lines):
            reserved_count = sum(cell in fixed for cell in line)
            formula = sum(fixed.get(cell, 0) for cell in line) + (3 - reserved_count) * umean
            assert F(sums[j], count) == formula
            assert abs(formula - 3 * bar) <= 3 * E
    for cell in reference[0]:
        assert F(reference[0][cell] + reference[1][cell], 2) in (F(8), F(12))
    # A common switch is not independent at its cells: these two variances differ.
    whole_variance = F((6 + 10) ** 2, 4)
    false_independent_variance = F(6 ** 2 + 10 ** 2, 4)
    assert whole_variance > false_independent_variance
    return {"exact_unused_pool_completions": completions,
            "whole_switch_variance": str(whole_variance),
            "false_independent_cell_variance": str(false_independent_variance),
            "scope": "centering identities; these arrays are not all-prime-line certificates"}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("source_archive", type=Path)
    args = p.parse_args()
    root = args.source_archive.resolve()
    bind_sources(root)
    targets = load_module(root / PREFIX / "code/hyperk_targets.py", "frozen_review_targets")
    resources = load_module(root / PREFIX / "code/hyperk_resources.py", "frozen_review_resources")
    result = {"source_revision": REVISION, "source_bindings": len(HASHES),
              "weights": weight_controls(targets), "completion": completion_controls(targets),
              "targets": fixture_controls(root), "ledger": ladder_controls(resources),
              "grids": grid_controls(), "centering": centering_controls(),
              "scope": "finite independent review controls; no asymptotic or full-arrangement certificate"}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
