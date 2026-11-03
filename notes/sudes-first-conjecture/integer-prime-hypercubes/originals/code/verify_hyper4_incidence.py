#!/usr/bin/env python3
"""Independent exact controls for hyper4_incidence.py.

Geometry comes from fixed/forward/reversed coordinate words, independently
of the producer's varying-coordinate representation.  All arithmetic is
integral.  These tests certify the supplied finite inputs and test proof
formulas; they are not an asymptotic proof or prime-arrangement certificate.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
from itertools import combinations, product
import json
from pathlib import Path
import random

import hyper4_incidence as producer
from signed_incidence import verify_smith_certificate


HERE = Path(__file__).resolve().parent
INPUTS = HERE.parent / "inputs"


def independent_lines(n):
    center = n // 2
    answer = set()
    for word in product(range(n + 2), repeat=4):
        if all(symbol < n for symbol in word):
            continue
        edge = []
        for t in range(n):
            point = tuple((t if symbol == n else n-1-t if symbol == n+1 else symbol)-center
                          for symbol in word)
            edge.append(point)
        answer.add(tuple(sorted(edge)))
    return tuple(sorted(answer))


def check_line_inventory(n, supplied):
    normalized = [tuple(sorted(tuple(point) for point in line)) for line in supplied]
    expected = independent_lines(n)
    if len(normalized) != len(set(normalized)) or tuple(sorted(normalized)) != expected:
        raise ValueError("Omitted, duplicated, or misidentified full signed line")


def independent_reduced(n):
    values = tuple(range(-(n//2), n//2+1))
    nonzero = tuple(x for x in values if x)
    columns = tuple(product(nonzero, repeat=4))
    rows = []
    for size in (2, 3, 4):
        for varying in combinations(range(4), size):
            remaining = tuple(j for j in range(4) if j not in varying)
            for signs_tail in product((1, -1), repeat=size-1):
                signs = (1,) + signs_tail
                for fixed in product(nonzero, repeat=4-size):
                    line = []
                    for t in values:
                        point = [None]*4
                        for i, sign in zip(varying, signs):
                            point[i] = sign*t
                        for i, value in zip(remaining, fixed):
                            point[i] = value
                        line.append(tuple(point))
                    row = []
                    for index in columns:
                        value = 0
                        for point in line:
                            term = 1
                            for coordinate, anchor in zip(point, index):
                                term *= int(coordinate == anchor)-int(coordinate == 0)
                            value += term
                        row.append(value)
                    rows.append(row)
    return rows


def integer_matrix(value, rows, columns):
    if (not isinstance(value, list) or len(value) != rows
            or any(not isinstance(row, list) or len(row) != columns
                   or any(type(entry) is not int for entry in row) for row in value)):
        raise ValueError("Malformed exact integer matrix")
    return value


def multiply(first, second):
    if not first or not second or len(first[0]) != len(second):
        raise ValueError("Matrix dimensions do not permit multiplication")
    result = [[0]*len(second[0]) for _ in first]
    for i, row in enumerate(first):
        for k, value in enumerate(row):
            if value:
                for j, other in enumerate(second[k]):
                    if other:
                        result[i][j] += value*other
    return result


def identity(length):
    return [[int(i == j) for j in range(length)] for i in range(length)]


def operation_replay(matrix, operations):
    a = [row[:] for row in matrix]
    if not isinstance(operations, list):
        raise ValueError("Operations must be a list")
    for operation in operations:
        if not isinstance(operation, list) or not operation:
            raise ValueError("Malformed elementary operation")
        tag, *arguments = operation
        arity = {"rs": 2, "cs": 2, "ra": 3, "ca": 3, "rn": 1}
        if tag not in arity or len(arguments) != arity[tag] or any(type(x) is not int for x in arguments):
            raise ValueError("Invalid elementary-operation schema")
        bound = len(a) if tag[0] == "r" else len(a[0])
        indices = arguments[:1] if tag == "rn" else arguments[:2]
        if any(not 0 <= index < bound for index in indices):
            raise ValueError("Out-of-range operation index")
        if tag[1] == "a" and indices[0] == indices[1]:
            raise ValueError("A self-addition is not an allowed unimodular operation")
        if tag == "rs":
            i, j = arguments
            a[i], a[j] = a[j], a[i]
        elif tag == "cs":
            i, j = arguments
            for row in a:
                row[i], row[j] = row[j], row[i]
        elif tag == "ra":
            i, j, coefficient = arguments
            a[i] = [x+coefficient*y for x, y in zip(a[i], a[j])]
        elif tag == "ca":
            i, j, coefficient = arguments
            for row in a:
                row[i] += coefficient*row[j]
        else:
            i, = arguments
            a[i] = [-x for x in a[i]]
    return a


def basis_pullback(vector, operations, kind):
    # Operations have already been independently validated by replay.
    answer = vector[:]
    for operation in reversed(operations):
        tag, *args = operation
        if tag[0] != kind:
            continue
        if tag.endswith("s"):
            answer[args[0]], answer[args[1]] = answer[args[1]], answer[args[0]]
        elif tag.endswith("a"):
            answer[args[1]] += args[2]*answer[args[0]]
        else:
            answer[args[0]] = -answer[args[0]]
    return answer


def checked_sparse(terms, size):
    result = [0]*size
    previous = -1
    if not isinstance(terms, list):
        raise ValueError("Sparse vector must be a list")
    for term in terms:
        if (not isinstance(term, list) or len(term) != 2
                or any(type(value) is not int for value in term)):
            raise ValueError("Malformed exact sparse term")
        index, value = term
        if not previous < index < size or not value:
            raise ValueError("Noncanonical sparse vector")
        previous = index
        result[index] = value
    return result


def verify_certificate(certificate):
    if not isinstance(certificate, dict) or certificate.get("kind") != "signed-hyper4-reduced-integer-incidence":
        raise ValueError("Wrong integer-incidence certificate kind")
    n = certificate.get("n")
    if type(n) is not int or n not in (3, 5):
        raise ValueError("This retained diagnostic concerns n=3 or n=5")
    matrix = independent_reduced(n)
    if certificate.get("rows") != len(matrix) or certificate.get("columns") != len(matrix[0]):
        raise ValueError("Wrong reduced matrix dimensions")
    if certificate.get("axis_rank") != n**4-(n-1)**4:
        raise ValueError("Incorrect axis rank")
    if certificate.get("full_line_count") != len(independent_lines(n)):
        raise ValueError("Incorrect full line count")
    rows, columns = len(matrix), len(matrix[0])
    method = certificate.get("method")
    if method == "elementary-operations":
        smith = certificate.get("smith")
        if not isinstance(smith, dict) or not verify_smith_certificate(matrix, smith):
            raise ValueError("Invalid integer elementary-operation Smith certificate")
        operation_replay(matrix, smith["operations"])
        factors = smith["diagonal"]
        rank = len(factors)
        kernels = [basis_pullback(identity(columns)[j], smith["operations"], "c")
                   for j in range(rank, columns)]
        dependencies = [basis_pullback(identity(rows)[i], smith["operations"], "r")
                        for i in range(rank, rows)]
        congruences = [(factor, basis_pullback(identity(rows)[i], smith["operations"], "r"))
                       for i, factor in enumerate(factors) if factor != 1]
    elif method == "unit-preconditioned-unimodular-block":
        prefix, rank = certificate.get("prefix"), certificate.get("tail_rank")
        if type(prefix) is not int or type(rank) is not int or not 0 <= prefix < min(rows, columns):
            raise ValueError("Invalid block dimensions")
        a = operation_replay(matrix, certificate.get("precondition_operations"))
        if any(a[i][j] != int(i == j) for i in range(rows) for j in range(columns)
               if i < prefix or j < prefix):
            raise ValueError("Preconditioner does not isolate the declared identity prefix")
        r, c = rows-prefix, columns-prefix
        if not 1 <= rank <= min(r, c):
            raise ValueError("Invalid tail rank")
        left = integer_matrix(certificate.get("left"), r, r)
        left_inverse = integer_matrix(certificate.get("left_inverse"), r, r)
        right = integer_matrix(certificate.get("right"), c, c)
        right_inverse = integer_matrix(certificate.get("right_inverse"), c, c)
        if multiply(left, left_inverse) != identity(r) or multiply(right, right_inverse) != identity(c):
            raise ValueError("The declared transforms are not integer-unimodular")
        square = integer_matrix(certificate.get("square"), rank, rank)
        trailing = [row[prefix:] for row in a[prefix:]]
        actual = multiply(multiply(left, trailing), right)
        expected = [[square[i][j] if i < rank and j < rank else 0 for j in range(c)] for i in range(r)]
        if actual != expected:
            raise ValueError("Integer transforms do not give the declared full block")
        smith = certificate.get("tail_smith")
        if (not isinstance(smith, dict) or not verify_smith_certificate(square, smith)
                or len(smith["diagonal"]) != rank):
            raise ValueError("Invalid exact Smith certificate of the nonsingular block")
        operation_replay(square, smith["operations"])
        factors = [1]*prefix+smith["diagonal"]
        pre = certificate["precondition_operations"]
        kernels = [basis_pullback([0]*prefix+[row[j] for row in right], pre, "c")
                   for j in range(rank, c)]
        dependencies = [basis_pullback([0]*prefix+row, pre, "r") for row in left[rank:]]
        congruences = []
        for i, factor in enumerate(smith["diagonal"]):
            if factor == 1:
                continue
            coefficients = basis_pullback(identity(rank)[i], smith["operations"], "r")
            row = [sum(coefficient*left[k][j] for k, coefficient in enumerate(coefficients)) for j in range(r)]
            congruences.append((factor, basis_pullback([0]*prefix+row, pre, "r")))
    else:
        raise ValueError("Unknown exact integer certificate method")

    recorded_kernel = certificate.get("kernel_basis")
    recorded_dependencies = certificate.get("dependency_basis")
    recorded_congruences = certificate.get("image_divisibility")
    if (not isinstance(recorded_kernel, list) or len(recorded_kernel) != len(kernels)
            or [checked_sparse(vector, columns) for vector in recorded_kernel] != kernels):
        raise ValueError("Wrong full reduced integer-kernel basis")
    if (not isinstance(recorded_dependencies, list) or len(recorded_dependencies) != len(dependencies)
            or [checked_sparse(vector, rows) for vector in recorded_dependencies] != dependencies):
        raise ValueError("Wrong reduced integer-dependency basis")
    if (not isinstance(recorded_congruences, list) or len(recorded_congruences) != len(congruences)
            or [(entry[0], checked_sparse(entry[1], rows)) for entry in recorded_congruences] != congruences):
        raise ValueError("Wrong integer image divisibility conditions")
    if any(sum(a*b for a, b in zip(row, vector)) for vector in kernels for row in matrix):
        raise ValueError("An exported array-kernel vector is not in the kernel")
    if any(sum(vector[i]*matrix[i][j] for i in range(rows))
           for vector in dependencies for j in range(columns)):
        raise ValueError("An exported line dependency is false")
    return {"n": n, "lines": certificate["full_line_count"],
            "full_rank": certificate["axis_rank"]+len(factors),
            "kernel_rank": (n-1)**4-len(factors),
            "nonunit_factors": [value for value in factors if value != 1]}


def rejects(function, *arguments):
    try:
        function(*arguments)
    except (ValueError, AssertionError, KeyError, TypeError, IndexError):
        return
    raise AssertionError("Negative control was incorrectly accepted")


def direct_image(n, sparse_array, keyed_geometry):
    return {key: sum(sparse_array.get(point, 0) for point in edge)
            for key, edge in keyed_geometry.items()}


def geometry_controls():
    for n, count in ((3, 272), (5, 888), (17, 23400)):
        geometry = producer.line_sets(n)
        independent = independent_lines(n)
        if len(geometry) != count or len(set(geometry.values())) != count:
            raise AssertionError("Wrong deduplicated line count")
        if {tuple(sorted(edge)) for edge in geometry.values()} != set(independent):
            raise AssertionError("Independent line generators disagree")
    supplied = list(producer.line_sets(3).values())
    rejects(check_line_inventory, 3, supplied[:-1])
    rejects(check_line_inventory, 3, supplied+[supplied[0]])
    bad = [set(edge) for edge in supplied]
    edge = next(i for i, line in enumerate(bad) if (0, 0, 0, 0) not in line)
    bad[edge].remove(next(iter(bad[edge])))
    bad[edge].add((0, 0, 0, 0))
    rejects(check_line_inventory, 3, bad)


def gadget_controls():
    n = 17
    geometry = producer.line_sets(n)
    zeros = dict.fromkeys(geometry, 0)
    # Test all body orientations and every resulting lower-family effect.
    for varying, signs in producer.families(4, 4):
        values = producer.cuboid(producer.body_cuboid(n, signs))
        image = direct_image(n, values, geometry)
        expected = zeros.copy()
        for size in (2, 3, 4):
            for subset in combinations(range(4), size):
                relative = tuple(signs[i]*signs[subset[0]] for i in subset)
                rest = tuple(i for i in range(4) if i not in subset)
                for bits in product((0, 1), repeat=len(rest)):
                    fixed = tuple(signs[i]*(1 if bit == 0 else i+2) for i, bit in zip(rest, bits))
                    expected[(subset, relative, fixed)] = (-1)**sum(bits)
        if image != expected:
            raise AssertionError("Body image or lower-family spill formula failed")

    # Each triple orientation; central/reflected endpoints are deliberate.
    for varying, signs in producer.families(3, 3):
        u, v = (-1, 1) if signs[-1] < 0 else (0, 1)
        values = producer.cuboid(producer.triple_cuboid(n, varying, signs, u, v))
        image = direct_image(n, values, geometry)
        expected_triple = {(varying, signs, (u,)): 1, (varying, signs, (v,)): -1}
        observed = {key: value for key, value in image.items() if len(key[0]) >= 3 and value}
        if observed != expected_triple:
            raise AssertionError("Triple transfer changed a protected family")
        if any(value for key, value in image.items() if len(key[0]) == 1):
            raise AssertionError("Triple transfer changed axes")
        for pair, pair_signs in producer.families(2, 2):
            if any(producer.matrix_trace(image, pair, pair_signs, sign, n) for sign in (1, -1)):
                raise AssertionError("Triple transfer introduced pair traces")

    for first in ((0, 1), (0, 2), (0, 3)):
        second = producer.complement(first)
        for sigma, tau in product((1, -1), repeat=2):
            values = producer.cuboid(producer.trace_cuboid(n, first, sigma, tau))
            image = direct_image(n, values, geometry)
            support = {key[:2] for key, value in image.items() if value}
            if support != {(first, (1, sigma)), (second, (1, tau))}:
                raise AssertionError("Coupled trace control has an extra family image")
            if (producer.matrix_trace(image, first, (1, sigma), tau, n) != 1
                    or producer.matrix_trace(image, second, (1, tau), sigma, n) != 1):
                raise AssertionError("Coupled trace coefficient is not one")

    # Coincident, opposite and unrelated anchored endpoints exercise traces 2.
    for varying, signs in producer.families(2, 2):
        for u, v in ((1, 1), (1, -1), (1, 2)):
            values = {}
            for coefficient, pairs in producer.pure_pair_terms(n, varying, signs[1], u, v):
                producer.add_sparse(values, producer.cuboid(pairs), coefficient)
            image = direct_image(n, values, geometry)
            if any(value for key, value in image.items() if key[:2] != (varying, signs)):
                raise AssertionError("Pure pair generator changes a protected family")
            if any(producer.matrix_trace(image, varying, signs, sign, n) for sign in (1, -1)):
                raise AssertionError("Pure pair generator has a nonzero trace")
    rejects(producer.cuboid, ((1, 1), (1, 2), (1, 3), (1, 4)))
    # The false center version is explicitly not an isolated body control.
    bad = producer.cuboid(((0, 1), (0, 2), (0, 3), (0, 4)))
    image = direct_image(n, bad, geometry)
    if sum(value != 0 for key, value in image.items() if len(key[0]) == 4) != 8:
        raise AssertionError("Central-body regression did not expose all eight coincidences")


def compatibility_and_lift_controls():
    n = 17
    values = producer.levels(n)
    random_source = random.Random(2026110204)
    sparse = {}
    for _ in range(80):
        point = tuple(random_source.choice(values) for _ in range(4))
        sparse[point] = random_source.randint(-9, 9)
    target = producer.line_sums(n, sparse)
    if producer.compatibility_errors(n, target):
        raise AssertionError("A real integer array violates a claimed necessary identity")
    if (producer.compatibility_errors(n, target, total=sum(sparse.values()))
            or not producer.compatibility_errors(n, target, total=sum(sparse.values())+1)):
        raise AssertionError("Fixed pool-total compatibility control failed")
    lift = producer.integer_lift(n, target)
    geometry = producer.line_sets(n)
    if direct_image(n, lift, geometry) != target:
        raise AssertionError("The constructive eventual integer lift failed")
    odd_target = {key: 2*value+n for key, value in target.items()}
    odd_lift = {point: 1+2*lift.get(point, 0) for point in product(values, repeat=4)}
    if direct_image(n, odd_lift, geometry) != odd_target or any(value % 2 != 1 for value in odd_lift.values()):
        raise AssertionError("Odd-lift congruence construction failed")
    constant = dict.fromkeys(target, n)
    congruence_lift = producer.integer_lift(n, constant, residue=1, modulus=2)
    if set(congruence_lift.values()) != {1} or len(congruence_lift) != n**4:
        raise AssertionError("Entry-congruence code path failed")
    bad = target.copy()
    bad[((0, 1), (1, 1), (1, 2))] += 1
    rejects(producer.integer_lift, n, bad)
    bad = constant.copy()
    bad[((0, 1, 2, 3), (1, 1, 1, 1), ())] += 1
    rejects(producer.integer_lift, n, bad, 1, 2)
    missing = target.copy()
    del missing[next(iter(missing))]
    rejects(producer.integer_lift, n, missing)
    rejects(producer.integer_lift, 15, dict.fromkeys(producer.line_keys(15), 0))
    zero = dict.fromkeys(target, 0)
    # A pair unit-trace matrix alone obeys A/P/T but must fail C.
    a, b = producer.selector(n, 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            zero[((0, 1), (1, 1), (x, y))] += (-1)**(i+j)
    errors = producer.compatibility_errors(n, zero)
    if not errors or any(error[0] != "pair-pair" for error in errors):
        raise AssertionError("Complementary-pair identity negative control failed")


def marker_residue_controls():
    n = 65
    values = producer.levels(n)
    edges = list(zip(values, values[1:]+values[:1]))
    plan = producer.marker_projection_plan(n, edges)
    paths = producer.routed_marker_paths(plan)
    producer.check_marker_paths(plan, paths)
    loads, diagonal_patterns = {}, 0
    matrices = []
    for template in plan["templates"]:
        cells = producer.template_cells(template["components"])
        matrices.append(cells)
        if any(x == y or x == -y for x, y in cells):
            diagonal_patterns += 1
        for cell in cells:
            loads[cell] = loads.get(cell, 0)+1
        if any(sum(value for (x, y), value in cells.items() if x == row) for row in values):
            raise AssertionError("Projected pattern has a row sum")
        if any(sum(value for (x, y), value in cells.items() if y == column) for column in values):
            raise AssertionError("Projected pattern has a column sum")
        if any(sum(value for (x, y), value in cells.items() if y == sign*x) for sign in (1, -1)):
            raise AssertionError("Projected pattern has a signed trace")
    if diagonal_patterns > 2*2**2*n:
        raise AssertionError("Too many graph-product patterns meet signed diagonals")
    if max(loads.values()) > 2**2+plan["max_orbit_use"]:
        raise AssertionError("Projection patterns exceed the proved target-cell load")
    target = {}
    for index in range(0, len(matrices), 79):
        coefficient = index % 17-8
        producer.add_sparse(target, matrices[index], coefficient)
    # All chosen moduli are composite or divide n except the modulus-one case.
    for modulus in (1, 5, 6, 13, 65):
        result = producer.residue_pair_decomposition(plan, target, modulus, paths)
        actual = {}
        for template, cells in zip(plan["templates"], matrices):
            e, f = template["source"]
            coefficient = result["coefficients"][e][f]
            if not 0 <= coefficient < modulus:
                raise AssertionError("Residue tensor coefficient is outside its paid interval")
            producer.add_sparse(actual, cells, coefficient)
        for coefficient, u, v in result["marker_flows"]:
            if not 0 <= coefficient < modulus:
                raise AssertionError("Marker prefix coefficient is outside its paid interval")
            first = producer.rectangle_cells(plan["markers"][u]["rectangle"])
            second = producer.rectangle_cells(plan["markers"][v]["rectangle"])
            if first.keys() & second.keys():
                raise AssertionError("Routed marker edge has an uncharged support collision")
            producer.add_sparse(actual, first, coefficient)
            producer.add_sparse(actual, second, -coefficient)
        if any((actual.get(cell, 0)-target.get(cell, 0)) % modulus for cell in product(values, repeat=2)):
            raise AssertionError("No-division tensor/marker residue routing failed")
    bad = deepcopy(paths)
    sign = next(sign for sign in (1, -1) if bad[sign]["edges"])
    u, _, position = bad[sign]["edges"][0]
    bad[sign]["edges"][0] = (u, u, position)
    rejects(producer.check_marker_paths, plan, bad)
    bad_target = target.copy()
    bad_target[(0, 1)] = bad_target.get((0, 1), 0)+1
    rejects(producer.residue_pair_decomposition, plan, bad_target, 6, paths)
    marker = plan["markers"][0]["rectangle"]
    rejects(producer.template_cells, [(1, marker), (-1, marker)])


def certificate_controls():
    summaries = []
    for n in (3, 5):
        path = INPUTS / f"hyper4_incidence_n{n}.json"
        certificate = json.loads(path.read_text())
        summaries.append(verify_certificate(certificate))
        if independent_reduced(n) != producer.reduced_axis_kernel_matrix(n)[2]:
            raise AssertionError("Direct geometric reduced matrix disagrees with contraction formula")
        bad = deepcopy(certificate)
        smith_key = "smith" if certificate["method"] == "elementary-operations" else "tail_smith"
        bad[smith_key]["diagonal"][-1] += 1
        rejects(verify_certificate, bad)
        bad = deepcopy(certificate)
        bad[smith_key]["operations"].append(["ra", 0, 0, 1])
        rejects(verify_certificate, bad)
        bad = deepcopy(certificate)
        bad["full_line_count"] -= 1
        rejects(verify_certificate, bad)
        bad = deepcopy(certificate)
        bad["dependency_basis"][0][0][1] *= 2
        rejects(verify_certificate, bad)
        if certificate["method"] == "unit-preconditioned-unimodular-block":
            bad = deepcopy(certificate)
            bad["right_inverse"][0][0] += 1
            rejects(verify_certificate, bad)
    return summaries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", type=Path)
    parser.add_argument("--skip-certificates", action="store_true")
    parser.add_argument("--markers-only", action="store_true")
    args = parser.parse_args()
    if args.verify:
        print(json.dumps(verify_certificate(json.loads(args.verify.read_text())), sort_keys=True))
        return
    if args.markers_only:
        marker_residue_controls()
        print("Marker projection and no-division residue controls passed (n=65; h=1,5,6,13,65).")
        return
    geometry_controls()
    gadget_controls()
    compatibility_and_lift_controls()
    marker_residue_controls()
    summaries = [] if args.skip_certificates else certificate_controls()
    print(json.dumps({"status": "passed", "finite_incidence": summaries,
                      "controls": ["independent full geometry", "all gadget orientations",
                                   "integer lift", "odd lift", "marker projection",
                                   "no-division residue paths", "negative controls"],
                      "scope": "Finite exact incidence evidence; no prime-array certificate."}, sort_keys=True))


if __name__ == "__main__":
    main()
