#!/usr/bin/env python3
"""Reproducible finite search; exhaustion is never an impossibility proof."""
from __future__ import annotations

import argparse
import json
import math
import random
from functools import lru_cache
from pathlib import Path

from prime_arrays import canonical_pool, certificate, element_prime, full_lines


def residue_obstruction(n: int, dimension: int, use_total: bool = True):
    """Export a complete binary proof tree; every propagation has a reason.

    A bit 1 denotes residue +1 modulo 1-omega and a bit 0 denotes -1.
    The proof consumer checks every step; search failure is not used as proof.
    """
    pool = canonical_pool("eisenstein", n ** dimension)
    lines = full_lines(n, dimension)
    plus = sum((a+b) % 3 == 1 for a, b in pool)
    allowed = [k for k in range(n+1) if (2*k-n) % 3]
    constraints = [(line, allowed, {"line": k}) for k, line in enumerate(lines)]
    if use_total:
        constraints.append((tuple(range(len(pool))), [plus], {"total": True}))
    nodes = 0
    def solve(assignment):
        nonlocal nodes
        nodes += 1
        forced = []
        while True:
            changed = False
            for cells, choices, reason in constraints:
                count = sum(assignment[j] == 1 for j in cells)
                unknown = [j for j in cells if assignment[j] == -1]
                possible = [k for k in choices if count <= k <= count+len(unknown)]
                if not possible:
                    return {"forced": forced, "contradiction": reason}, None
                if unknown and (possible == [count] or possible == [count+len(unknown)]):
                    value = int(possible == [count+len(unknown)])
                    for j in unknown:
                        assignment[j] = value
                        forced.append({"cell": j, "value": value, "reason": reason})
                    changed = True
            if not changed:
                break
        unknown = [j for j in range(len(pool)) if assignment[j] == -1]
        if not unknown:
            return None, assignment
        j = max(unknown, key=lambda cell: sum(sum(assignment[x] >= 0 for x in line)+1
                                               for line in lines if cell in line))
        children = []
        for value in (0, 1):
            child = assignment.copy()
            child[j] = value
            proof, witness = solve(child)
            if witness is not None:
                return None, witness
            children.append(proof)
        return {"forced": forced, "branch_cell": j, "children": children}, None
    proof, witness = solve([-1] * len(pool))
    if witness is not None:
        raise ValueError("residue system is feasible; no obstruction: " + str(witness))
    return {"format": "quadratic-prime-obstruction-v1", "ring": "eisenstein",
            "n": n, "dimension": dimension, "family": "full-signed-coordinate-lines",
            "pool": list(map(list, pool)), "residue_ideal": "1-omega",
            "plus_count": plus, "minus_count": len(pool)-plus,
            "uses_total_count": use_total, "allowed_line_plus_counts": allowed,
            "proof": proof, "producer_node_count": nodes,
            "provenance": {"method": "complete-binary-residue-search-with-checked-propagation"}}


def search(ring: str, n: int, dimension: int, seed: int, steps: int, restarts: int):
    pool = canonical_pool(ring, n ** dimension)
    lines = full_lines(n, dimension)
    incident = [set() for _ in pool]
    for k, line in enumerate(lines):
        for j in line:
            incident[j].add(k)
    affected = {(i, j): sorted(incident[i] ^ incident[j])
                for i in range(len(pool)) for j in range(i + 1, len(pool))}
    rng = random.Random(seed)
    @lru_cache(None)
    def cost(a, b):
        return int(not element_prime((a, b), ring))
    best = len(lines)
    total_steps = 0
    for restart in range(restarts):
        array = pool.copy()
        rng.shuffle(array)
        sums = [tuple(sum(array[j][d] for j in line) for d in (0, 1)) for line in lines]
        bad = [cost(*z) for z in sums]
        score = sum(bad)
        for step in range(steps):
            total_steps += 1
            if score < best:
                best = score
                print(json.dumps({"ring": ring, "n": n, "dimension": dimension,
                                  "restart": restart, "step": step, "best_bad": best}), flush=True)
            if score == 0:
                return array, {"method": "seeded-swap-annealing", "seed": seed,
                               "steps_per_restart": steps, "restarts": restarts,
                               "found_restart": restart, "found_step": step,
                               "total_steps": total_steps}
            if rng.random() < 0.8:
                k = rng.choice([k for k, v in enumerate(bad) if v])
                i = rng.choice(lines[k])
                j = rng.randrange(len(pool) - 1)
                if j >= i:
                    j += 1
            else:
                i, j = rng.sample(range(len(pool)), 2)
            if i > j:
                i, j = j, i
            a, b = array[j][0] - array[i][0], array[j][1] - array[i][1]
            changes = []
            delta = 0
            for k in affected[i, j]:
                sign = 1 if k in incident[i] else -1
                new_sum = (sums[k][0] + sign * a, sums[k][1] + sign * b)
                new_bad = cost(*new_sum)
                changes.append((k, new_sum, new_bad))
                delta += new_bad - bad[k]
            temperature = 0.15 + 0.7 * (1 - (step % 5000) / 5000)
            if delta <= 0 or rng.random() < math.exp(-delta / temperature):
                array[i], array[j] = array[j], array[i]
                score += delta
                for k, new_sum, new_bad in changes:
                    sums[k], bad[k] = new_sum, new_bad
    return None, {"best_bad": best, "seed": seed, "steps": total_steps}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ring", choices=("gaussian", "eisenstein"), required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--dimension", type=int, choices=(2, 3), default=2)
    parser.add_argument("--seed", type=int, default=20261102)
    parser.add_argument("--steps", type=int, default=100000)
    parser.add_argument("--restarts", type=int, default=30)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--obstruction", action="store_true")
    parser.add_argument("--ignore-total-count", action="store_true")
    args = parser.parse_args()
    if args.obstruction:
        if args.ring != "eisenstein":
            parser.error("this residue-proof producer supports the Eisenstein ramified ideal")
        obj = residue_obstruction(args.n, args.dimension, not args.ignore_total_count)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(obj, indent=2) + "\n")
        print(json.dumps({"status": "residue-obstruction-certificate", "nodes": obj["producer_node_count"],
                          "output": str(args.output)}))
        return
    array, metadata = search(args.ring, args.n, args.dimension, args.seed, args.steps, args.restarts)
    if array is None:
        print(json.dumps({"status": "search-exhausted-not-an-obstruction", **metadata}))
        raise SystemExit(2)
    obj = certificate(args.ring, args.n, args.dimension, array, metadata)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(obj, indent=2) + "\n")
    print(json.dumps({"status": "constructed", "output": str(args.output), **metadata}))


if __name__ == "__main__":
    main()
