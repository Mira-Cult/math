#!/usr/bin/env python3
"""Nonauthor controls for kernel research at 99cd33eb8f91682342a671b46599f43b1365ed7c.

Author: /root/incidence_review. Pass an exact git-archive root as argument.
Finite tests of local constructions and obstructions, not a BK(d) proof.
"""

from collections import Counter, defaultdict
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import json
import sys


REVISION = "99cd33eb8f91682342a671b46599f43b1365ed7c"
HASHES = {
    "manuscripts/hyperk_kernel_research.md": "c4dc2db4da2e502f0bc8d564e44c2f504b13e9e0fae7ae77b780cfdb70838f44",
    "code/hyperk_kernel_research.py": "4c96f78d90110752293dc798059f87c091b7d6578ea63c0734cc3541d3d2cc34",
    "code/check_hyperk_certificate.py": "ed71e345fdc92c30303657a11ef34909d42a5413ea9eb00a1c59ae645f94dd76",
    "inputs/hyperk-square3-arrangement.json": "b2367b8e8edc6d506054751566f0ba7ddbfc4e92f2213bd641316ea1f9d18d4f",
}


def tidy(a):
    return {x: z for x, z in a.items() if z}


def accumulate(target, source, multiplier=1):
    for x, z in source.items():
        target[x] += multiplier * z


def tensor(factors, d):
    out = {}
    for items in product(*(list(f.items()) for _, f in factors)):
        x, z = [None] * d, 1
        for (coords, _), (point, coefficient) in zip(factors, items):
            for i, v in zip(coords, point):
                assert x[i] is None
                x[i] = v
            z *= coefficient
        assert None not in x
        assert tuple(x) not in out
        out[tuple(x)] = z
    return tidy(out)


def raw(pairs):
    return tensor([((i,), {(u,): 1, (v,): -1}) for i, (u, v) in enumerate(pairs)], len(pairs))


def all_blocks(d):
    for word in product((-1, 0, 1), repeat=d):
        block = tuple(i for i, x in enumerate(word) if x)
        if len(block) >= 2 and word[block[0]] == 1:
            yield block, tuple(word[i] for i in block)


def collections(d):
    blocks = tuple(all_blocks(d))
    yield ()
    for count in range(1, d // 2 + 1):
        for pi in combinations(blocks, count):
            covered = [i for block, _ in pi for i in block]
            if len(covered) == len(set(covered)):
                yield pi


def signature(a, d):
    """Independent step-word enumeration of sparse full-line images."""
    sums = defaultdict(int)
    for word in product((-1, 0, 1), repeat=d):
        varying = tuple(i for i, s in enumerate(word) if s)
        if not varying or word[varying[0]] != 1:
            continue
        signs = tuple(word[i] for i in varying)
        for x, z in a.items():
            t = x[varying[0]]
            if all(x[i] == word[i] * t for i in varying):
                sums[varying, signs, tuple(x[i] for i in range(d) if not word[i])] += z
    return tidy(sums)


def witnesses(pairs, block):
    coords, signs = block
    factors = [{u: 1, v: -1} for u, v in pairs]
    out = []
    for t in pairs[coords[0]]:
        z = 1
        for i, s in zip(coords, signs):
            z *= factors[i].get(s * t, 0)
        if z:
            out.append((t, z))
    return out


def palette_projector(kmod, pairs):
    d = len(pairs)
    alphabets, _ = kmod.selector_invoices(d)
    a = alphabets[d]
    w = 2 * ((3 ** d - 1) // 2 - d)
    H = 2 * d + w * a + 1
    m = H * a + 1
    assert all(abs(t) <= m for pair in pairs for t in pair)
    used = {abs(t) for pair in pairs for t in pair if t}
    shared = {}
    allocated = []
    center_count = 0
    for block in all_blocks(d):
        coords, signs = block
        q, count = kmod.pure_selector(len(coords))
        combined = defaultdict(int)
        for t, epsilon in witnesses(pairs, block):
            rho = abs(t) - 1 if t else 0
            for h in range(H):
                labels = [1 + ((rho + h * a + j - 1) % m) for j in range(1, count + 1)]
                if set(labels).isdisjoint(used):
                    break
            else:
                raise AssertionError("finite palette exhausted")
            assert len(set(labels)) == count
            used.update(labels)
            allocated.append((t, h, tuple(labels)))
            center_count += int(t == 0)
            embedded = {tuple(s * labels[v - 1] for s, v in zip(signs, x)): epsilon * z
                        for x, z in q.items()}
            assert set(combined).isdisjoint(embedded)
            accumulate(combined, embedded)
        shared[block] = tidy(combined)
    result = {}
    for pi in collections(d):
        covered = {i for block, _ in pi for i in block}
        factors = [(block, shared[block, signs]) for block, signs in pi]
        factors.extend(((i,), {(pairs[i][0],): 1, (pairs[i][1],): -1})
                       for i in range(d) if i not in covered)
        term = tensor(factors, d)
        assert set(result).isdisjoint(term)
        result.update({x: (-1) ** len(pi) * z for x, z in term.items()})
    assert set(result.values()) <= {-1, 1}
    assert not signature(result, d)
    return result, allocated, center_count, (m, H, a)


def palette_controls(kmod):
    answers = []
    for d in (2, 3):
        alphabets, _ = kmod.selector_invoices(d)
        a = alphabets[d]
        w = 2 * ((3 ** d - 1) // 2 - d)
        H = 2 * d + w * a + 1
        m = H * a + 1
        vertices = [0, 1, -1, m, m - 1, 2, -2, -m]
        edges = list(zip(vertices, vertices[1:] + vertices[:1]))
        loads = Counter()
        centers = 0
        raw_count = 0
        for pairs in product(edges, repeat=d):
            projected, allocated, zero_witnesses, _ = palette_projector(kmod, pairs)
            loads.update(projected.keys())
            centers += zero_witnesses
            raw_count += 1
            for t, h, labels in allocated:
                y = labels[0]
                possible = set()
                for palette in range(H):
                    for j in range(1, a + 1):
                        rho = (y - 1 - palette * a - j + 1) % m
                        possible.update((rho + 1, -rho - 1))
                        if rho == 0:
                            possible.add(0)
                assert t in possible
                assert len(possible) <= 3 * H * a
        p = sum(1 for _ in collections(d))
        bound = p * 2 ** d * (3 * H * a) ** (d // 2)
        assert max(loads.values()) <= bound
        assert centers
        answers.append({"d": d, "n": 2 * m + 1, "degree": 2,
                        "raw_products": raw_count, "center_witnesses": centers,
                        "max_point_incidence": max(loads.values()), "bound": bound})
    # Saturates the number of witnesses and tests common absolute values at d=4.
    projected, allocated, centers, params = palette_projector(kmod, ((-1, 1),) * 4)
    assert len(allocated) == 2 * ((3 ** 4 - 1) // 2 - 4)
    assert not centers
    answers.append({"d": 4, "witnesses": len(allocated), "support": len(projected),
                    "ambient_order": 2 * params[0] + 1})
    return answers


def slice_array(a, d, pi, parameters):
    prescribed = {i: s * t for (block, signs), t in zip(pi, parameters)
                  for i, s in zip(block, signs)}
    free = tuple(i for i in range(d) if i not in prescribed)
    result = {tuple(x[i] for i in free): z for x, z in a.items()
              if all(x[i] == v for i, v in prescribed.items())}
    return free, result


def coherent_identity(kmod, expansion, d, pi):
    whole = defaultdict(int)
    for coefficient, pairs in expansion:
        accumulate(whole, raw(pairs), coefficient)
    whole = tidy(whole)
    assert not signature(whole, d)
    lookup = {}
    next_label = 10000

    def selector(block, t):
        nonlocal next_label
        key = block, t
        if key not in lookup:
            coords, signs = block
            q, count = kmod.pure_selector(len(coords))
            lookup[key] = {tuple(s * (v + next_label) for s, v in zip(signs, x)): z
                           for x, z in q.items()}
            next_label += count
        return lookup[key]

    lhs = defaultdict(int)
    parameter_values = [set() for _ in pi]
    covered = {i for block, _ in pi for i in block}
    for coefficient, pairs in expansion:
        factors = []
        for index, block in enumerate(pi):
            combined = defaultdict(int)
            for t, epsilon in witnesses(pairs, block):
                parameter_values[index].add(t)
                accumulate(combined, selector(block, t), epsilon)
            factors.append((block[0], tidy(combined)))
        factors.extend(((i,), {(pairs[i][0],): 1, (pairs[i][1],): -1})
                       for i in range(d) if i not in covered)
        accumulate(lhs, tensor(factors, d), coefficient)
    rhs = defaultdict(int)
    slices = {}
    for parameters in product(*parameter_values):
        free, sliced = slice_array(whole, d, pi, parameters)
        assert not signature(sliced, len(free))
        slices[parameters] = sliced
        factors = [(block[0], selector(block, t)) for block, t in zip(pi, parameters)]
        if free:
            factors.append((free, sliced))
        elif not sliced:
            continue
        # In zero free dimensions the scalar slice must multiply the tensor.
        term = tensor(factors, d)
        accumulate(rhs, term, sliced.get((), 1) if not free else 1)
    assert tidy(lhs) == tidy(rhs)
    for index in range(len(pi)):
        margins = defaultdict(lambda: defaultdict(int))
        for parameters, sliced in slices.items():
            others = parameters[:index] + parameters[index + 1:]
            accumulate(margins[others], sliced)
        assert all(not tidy(margin) for margin in margins.values())
    return len(tidy(lhs)), any(0 in values for values in parameter_values)


def coherent_controls(kmod):
    r = [((1, 2), (1, 3)), ((5, 6), (5, 7))]
    s = [((11, 12), (11, 13)), ((15, 16), (15, 17))]
    expansion = [((-1) ** (i + j), left + right) for i, left in enumerate(r)
                 for j, right in enumerate(s)]
    partitions = [(((0, 1), (1, 1)),),
                  (((0, 1), (1, 1)), ((2, 3), (1, 1))),
                  (((0, 1), (1, -1)),), (((0, 2), (1, 1)),)]
    sizes = [coherent_identity(kmod, expansion, 4, pi)[0] for pi in partitions]
    assert sizes[0] and sizes[1] and not sizes[2] and not sizes[3]
    # A full-kernel input with central slices, expanded in anchored axis tensors.
    central = kmod.local_projector(((0, 1), (0, -1), (0, 2)))
    anchored = [(value, tuple((u, 0) for u in x)) for x, value in central.items() if all(x)]
    rebuilt = defaultdict(int)
    for coefficient, pairs in anchored:
        accumulate(rebuilt, raw(pairs), coefficient)
    assert tidy(rebuilt) == central
    size, saw_center = coherent_identity(kmod, anchored, 3, (((0, 1), (1, -1)),))
    assert saw_center and size
    return {"noncentral_partition_output_supports": sizes,
            "central_output_support": size, "central_anchor_terms": len(anchored),
            "boundary": "unweighted slice marginals vanish; embedded marker sum need not vanish"}


def arrangement_control(problem, verifier):
    data = json.loads((problem / "inputs/hyperk-square3-arrangement.json").read_text())
    result = verifier.verify(data)
    # Independent sieve for this finite input, not the verifier's trial division.
    values = data["values"]
    limit = max(max(values), max(record["sum"] for record in data["constraints"]))
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for p in range(2, limit + 1):
        if sieve[p]:
            for multiple in range(p * p, limit + 1, p):
                sieve[multiple] = False
    assert sorted(values) == [p for p in range(3, limit + 1) if sieve[p]][:9]
    grid = dict(zip(product(range(-1, 2), repeat=2), values))
    sums = signature(grid, 2)
    assert len(sums) == 8
    assert all(sieve[total] for total in sums.values())
    assert sorted(sums.values()) == sorted(record["sum"] for record in data["constraints"])
    return {"k": result["k"], "n": result["n"], "lines": len(sums),
            "scope": "one exact finite arrangement only"}


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: hyperk_kernel_controls.py EXACT_ARCHIVE_ROOT")
    problem = Path(sys.argv[1]).resolve() / "problems/prime-arrays-beyond-square"
    for path, digest in HASHES.items():
        assert sha256((problem / path).read_bytes()).hexdigest() == digest, path
    sys.path.insert(0, str(problem / "code"))
    import hyperk_kernel_research as kmod
    import check_hyperk_certificate as verifier
    results = {"revision": REVISION, "python": sys.version.split()[0],
               "palette": palette_controls(kmod), "coherent_identity": coherent_controls(kmod),
               "arrangement": arrangement_control(problem, verifier), "status": "PASS"}
    print(json.dumps(results, sort_keys=True))


if __name__ == "__main__":
    main()
