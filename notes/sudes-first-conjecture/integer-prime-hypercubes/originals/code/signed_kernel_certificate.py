#!/usr/bin/env python3
"""Full-matrix integer-kernel certificates for signed cubes of orders 3 and 5.

The incidence matrix A has one row for each full signed-coordinate line,
ordered lexicographically by its sorted cell list, and one column for each
cell (x,y,z), numbered x*n*n+y*n+z.  All indices are zero based.

The certificate gives unimodular U,V with U*A*V=D in Smith form.  Sparse
columns V[:,rank:] are a basis of the FULL integer array kernel; sparse rows
U[rank:,:] are a basis of the FULL integer line-dependency lattice.  An
integer line target b is in the image precisely when all dependency rows
annihilate b and every exported nonunit Smith row has scalar product with
b divisible by its invariant factor.  Conditions for factor one are
automatic and are explicitly omitted.

The producer imports only the existing Smith producer and the independent
check_signed_cube.full_lines geometry.  An explicitly logged unit-pivot
preconditioning pass keeps the exported transformations small; the frozen
Smith producer then finishes that equivalent matrix.  The verifier independently generates
the full geometry from fixed/forward/reversed coordinate words, replays the
allowed operations, reconstructs U,V, directly checks U*A*V=D, and checks
every basis and divisibility row.  Unimodularity comes from the validated
elementary operations, so free columns and zero rows span the integer
lattices, not merely their rational spans.

Usage from the repository root:
  python3 -B problems/prime-arrays-beyond-square/code/signed_kernel_certificate.py --self-test
  python3 -B problems/prime-arrays-beyond-square/code/signed_kernel_certificate.py --certificate --n 3
  python3 -B problems/prime-arrays-beyond-square/code/signed_kernel_certificate.py --verify FILE

Certificates are finite exact diagnostics.  They make no positivity,
prime-entry, prescribed-pool, bounded-coefficient, or asymptotic assertion.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
from itertools import product
import json
from pathlib import Path

from check_signed_cube import full_lines
from signed_incidence import smith_certificate


KIND = "full-signed-cube-integer-kernel-certificate"
CELL_ORDER = "x*n*n+y*n+z; x,y,z=0,...,n-1"
LINE_ORDER = "lexicographic sorted cell-index tuples"
SCOPE = "Finite integer incidence diagnostic only; no prescribed-pool or asymptotic conclusion."


def integer(value, label):
    if type(value) is not int:
        raise ValueError(f"{label} must be an exact integer")
    return value


def order(n):
    if type(n) is not int or n not in (3, 5):
        raise ValueError("This diagnostic is restricted to n=3 and n=5")
    return n


def identity(size):
    return [[int(i == j) for j in range(size)] for i in range(size)]


def sparse(vector):
    return [[index, value] for index, value in enumerate(vector) if value]


def dense(terms, length, label):
    if not isinstance(terms, list):
        raise ValueError(f"{label} must be a list of sparse terms")
    result = [0] * length
    previous = -1
    for term in terms:
        if not isinstance(term, list) or len(term) != 2:
            raise ValueError(f"Malformed sparse term in {label}")
        index, coefficient = term
        integer(index, f"{label} index")
        integer(coefficient, f"{label} coefficient")
        if not previous < index < length or not coefficient:
            raise ValueError(f"Noncanonical index, duplicate, or zero in {label}")
        result[index] = coefficient
        previous = index
    return result


def independent_lines(n):
    """Verifier geometry; does not call the producer's full_lines helper."""
    result = set()
    for word in product(range(n + 2), repeat=3):
        if all(symbol < n for symbol in word):
            continue
        edge = []
        for parameter in range(n):
            point = [parameter if symbol == n else n - 1 - parameter
                     if symbol == n + 1 else symbol for symbol in word]
            edge.append(point[0] * n * n + point[1] * n + point[2])
        result.add(tuple(sorted(edge)))
    return tuple(sorted(result))


def incidence(lines, cells):
    return [[int(cell in line) for cell in range(cells)] for line in lines]


def unit_pivot_precondition(matrix):
    """Unimodularly remove available unit pivots, minimizing a fill proxy.

    The deterministic pivot minimizes (row_nonzeros-1)*(column_nonzeros-1),
    then the row and column indices.  This is solely a size optimization:
    the verifier checks the complete operation log without trusting this
    pivot choice or assuming that the remaining matrix is already Smith.
    """
    current = [row[:] for row in matrix]
    rows, columns = len(current), len(current[0])
    operations = []
    pivot = 0
    while pivot < min(rows, columns):
        row_nonzeros = [sum(bool(value) for value in row[pivot:]) for row in current]
        column_nonzeros = [sum(bool(current[row][column]) for row in range(pivot, rows))
                           for column in range(columns)]
        candidates = [((row_nonzeros[row] - 1) * (column_nonzeros[column] - 1), row, column)
                      for row in range(pivot, rows) for column in range(pivot, columns)
                      if abs(current[row][column]) == 1]
        if not candidates:
            break
        _, row, column = min(candidates)
        if row != pivot:
            current[row], current[pivot] = current[pivot], current[row]
            operations.append(["rs", row, pivot])
        if column != pivot:
            for data in current:
                data[column], data[pivot] = data[pivot], data[column]
            operations.append(["cs", column, pivot])
        if current[pivot][pivot] < 0:
            current[pivot] = [-value for value in current[pivot]]
            operations.append(["rn", pivot])
        for row in range(pivot + 1, rows):
            multiplier = -current[row][pivot]
            if multiplier:
                current[row] = [x + multiplier * y for x, y in zip(current[row], current[pivot])]
                operations.append(["ra", row, pivot, multiplier])
        for column in range(pivot + 1, columns):
            multiplier = -current[pivot][column]
            if multiplier:
                for data in current:
                    data[column] += multiplier * data[pivot]
                operations.append(["ca", column, pivot, multiplier])
        pivot += 1
    return current, operations


def replay(matrix, smith):
    """Validate and replay operations, simultaneously extracting U and V."""
    rows, columns = len(matrix), len(matrix[0])
    if (not isinstance(smith, dict) or set(smith) != {"shape", "diagonal", "operations"}
            or smith["shape"] != [rows, columns]
            or any(type(v) is not int for v in smith["shape"])):
        raise ValueError("Smith shape or schema mismatch")
    diagonal = smith["diagonal"]
    if (not isinstance(diagonal, list) or len(diagonal) > min(rows, columns)
            or any(type(value) is not int or value <= 0 for value in diagonal)
            or any(right % left for left, right in zip(diagonal, diagonal[1:]))):
        raise ValueError("Invalid positive Smith divisibility chain")
    if not isinstance(smith["operations"], list):
        raise ValueError("Elementary operations must be a list")
    transformed = [row[:] for row in matrix]
    left, right = identity(rows), identity(columns)
    for operation in smith["operations"]:
        if not isinstance(operation, list) or not operation or type(operation[0]) is not str:
            raise ValueError("Malformed elementary operation")
        tag, *arguments = operation
        expected_arity = {"rs": 2, "cs": 2, "ra": 3, "ca": 3, "rn": 1}
        if tag not in expected_arity or len(arguments) != expected_arity[tag]:
            raise ValueError("Unknown elementary operation or wrong arity")
        if any(type(value) is not int for value in arguments):
            raise ValueError("Elementary-operation arguments must be integers")
        bound = rows if tag[0] == "r" else columns
        indices = arguments if tag.endswith("s") else arguments[:2] if tag.endswith("a") else arguments
        if any(not 0 <= index < bound for index in indices):
            raise ValueError("Elementary-operation index out of bounds")
        if tag.endswith("a") and arguments[0] == arguments[1]:
            raise ValueError("Adding a row or column to itself is not an allowed operation")
        matrices = (transformed, left) if tag[0] == "r" else (transformed, right)
        if tag == "rs":
            i, j = arguments
            for current in matrices:
                current[i], current[j] = current[j], current[i]
        elif tag == "cs":
            i, j = arguments
            for current in matrices:
                for row in current:
                    row[i], row[j] = row[j], row[i]
        elif tag == "ra":
            destination, source, multiplier = arguments
            for current in matrices:
                current[destination] = [x + multiplier * y
                                        for x, y in zip(current[destination], current[source])]
        elif tag == "ca":
            destination, source, multiplier = arguments
            for current in matrices:
                for row in current:
                    row[destination] += multiplier * row[source]
        else:
            index = arguments[0]
            for current in matrices:
                current[index] = [-value for value in current[index]]
    rank = len(diagonal)
    expected = [[diagonal[i] if i == j and i < rank else 0
                 for j in range(columns)] for i in range(rows)]
    if transformed != expected:
        raise ValueError("Elementary operations do not yield the declared Smith form")
    return left, right, expected


def multiply(first, second):
    """Direct exact matrix multiplication, separate from operation replay."""
    if not first or not second or len(first[0]) != len(second):
        raise ValueError("Matrix product shape mismatch")
    result = [[0] * len(second[0]) for _ in first]
    for row_index, row in enumerate(first):
        for inner, coefficient in enumerate(row):
            if coefficient:
                for column, value in enumerate(second[inner]):
                    if value:
                        result[row_index][column] += coefficient * value
    return result


def produce(n):
    n = order(n)
    lines = full_lines(n)
    matrix = incidence(lines, n ** 3)
    conditioned, prefix_operations = unit_pivot_precondition(matrix)
    suffix = smith_certificate(conditioned)
    smith = {"shape": list(suffix["shape"]), "diagonal": suffix["diagonal"],
             "operations": prefix_operations + [list(operation) for operation in suffix["operations"]]}
    left, right, _ = replay(matrix, smith)
    rank = len(smith["diagonal"])
    left_sparse = [sparse(row) for row in left]
    right_sparse = [sparse(column) for column in zip(*right)]
    return {
        "kind": KIND,
        "schema_version": 1,
        "n": n,
        "cell_order": CELL_ORDER,
        "line_order": LINE_ORDER,
        "lines": [list(line) for line in lines],
        "rank": rank,
        "array_kernel_rank": n ** 3 - rank,
        "line_dependency_rank": len(lines) - rank,
        "smith": smith,
        "left_transform_rows": left_sparse,
        "right_transform_columns": right_sparse,
        "array_kernel_basis": [
            {"free_column": column, "terms": right_sparse[column]}
            for column in range(rank, n ** 3)
        ],
        "line_dependency_basis": [
            {"zero_row": row, "terms": left_sparse[row]}
            for row in range(rank, len(lines))
        ],
        "image_criterion": {
            "unit_factor_conditions_omitted": True,
            "zero_equations_are_line_dependency_basis": True,
            "divisibility": [
                {"row": row, "divisor": divisor, "terms": left_sparse[row]}
                for row, divisor in enumerate(smith["diagonal"]) if divisor > 1
            ],
        },
        "scope": SCOPE,
    }


def verify(certificate):
    if not isinstance(certificate, dict) or certificate.get("kind") != KIND:
        raise ValueError("Wrong certificate kind")
    if type(certificate.get("schema_version")) is not int or certificate["schema_version"] != 1:
        raise ValueError("Unsupported certificate schema")
    n = order(certificate["n"])
    if certificate.get("cell_order") != CELL_ORDER or certificate.get("line_order") != LINE_ORDER:
        raise ValueError("Unknown cell or line indexing convention")
    lines = independent_lines(n)
    if len(lines) != 3 * n * n + 6 * n + 4 or any(len(line) != n for line in lines):
        raise AssertionError("Independent full-line geometry has the wrong dimension")
    supplied_lines = certificate["lines"]
    if not isinstance(supplied_lines, list):
        raise ValueError("Canonical lines must be a list")
    for line in supplied_lines:
        if (not isinstance(line, list) or len(line) != n
                or any(type(cell) is not int or not 0 <= cell < n ** 3 for cell in line)
                or line != sorted(set(line))):
            raise ValueError("Malformed canonical line")
    if supplied_lines != [list(line) for line in lines]:
        raise ValueError("A full signed line is omitted, repeated, misidentified, or out of order")
    matrix = incidence(lines, n ** 3)
    rows, columns = len(lines), n ** 3
    left, right, diagonal_matrix = replay(matrix, certificate["smith"])
    diagonal = certificate["smith"]["diagonal"]
    rank = len(diagonal)
    for field, expected in (("rank", rank), ("array_kernel_rank", columns - rank),
                            ("line_dependency_rank", rows - rank)):
        if integer(certificate[field], field) != expected:
            raise ValueError(f"Wrong {field}")

    left_terms, right_terms = certificate["left_transform_rows"], certificate["right_transform_columns"]
    if not isinstance(left_terms, list) or len(left_terms) != rows:
        raise ValueError("Incomplete left transformation")
    if not isinstance(right_terms, list) or len(right_terms) != columns:
        raise ValueError("Incomplete right transformation")
    supplied_left = [dense(terms, rows, f"U row {i}") for i, terms in enumerate(left_terms)]
    supplied_right_columns = [dense(terms, columns, f"V column {j}")
                              for j, terms in enumerate(right_terms)]
    supplied_right = [list(row) for row in zip(*supplied_right_columns)]
    if supplied_left != left or supplied_right != right:
        raise ValueError("Exported U or V differs from the unimodular replay")
    if multiply(multiply(supplied_left, matrix), supplied_right) != diagonal_matrix:
        raise ValueError("Direct exact multiplication failed U*A*V=D")

    kernel = certificate["array_kernel_basis"]
    if not isinstance(kernel, list) or len(kernel) != columns - rank:
        raise ValueError("Incomplete full-array integer kernel basis")
    for free_column, record in enumerate(kernel, rank):
        if not isinstance(record, dict) or set(record) != {"free_column", "terms"}:
            raise ValueError("Malformed full-array kernel record")
        if integer(record["free_column"], "free column") != free_column:
            raise ValueError("Kernel basis is not indexed by all free columns of V")
        vector = dense(record["terms"], columns, "array-kernel vector")
        if any(sum(vector[cell] for cell in line) for line in lines):
            raise ValueError("A claimed array-kernel vector changes a line sum")
        if vector != supplied_right_columns[free_column]:
            raise ValueError("Kernel vector is not the certified free column of V")

    dependencies = certificate["line_dependency_basis"]
    if not isinstance(dependencies, list) or len(dependencies) != rows - rank:
        raise ValueError("Incomplete full line-dependency basis")
    for zero_row, record in enumerate(dependencies, rank):
        if not isinstance(record, dict) or set(record) != {"zero_row", "terms"}:
            raise ValueError("Malformed line-dependency record")
        if integer(record["zero_row"], "zero row") != zero_row:
            raise ValueError("Dependencies do not index every zero row of U")
        vector = dense(record["terms"], rows, "line-dependency vector")
        cell_coefficients = [0] * columns
        for coefficient, line in zip(vector, lines):
            for cell in line:
                cell_coefficients[cell] += coefficient
        if any(cell_coefficients):
            raise ValueError("A claimed line dependency is not an identity on arrays")
        if vector != supplied_left[zero_row]:
            raise ValueError("Dependency vector is not the certified zero row of U")

    criterion = certificate["image_criterion"]
    if (not isinstance(criterion, dict) or
            set(criterion) != {"unit_factor_conditions_omitted", "zero_equations_are_line_dependency_basis", "divisibility"}
            or criterion["unit_factor_conditions_omitted"] is not True
            or criterion["zero_equations_are_line_dependency_basis"] is not True):
        raise ValueError("Image criterion does not specify the complete Smith conditions")
    conditions = criterion["divisibility"]
    required_rows = [(row, divisor) for row, divisor in enumerate(diagonal) if divisor > 1]
    if not isinstance(conditions, list) or len(conditions) != len(required_rows):
        raise ValueError("Missing or additional nonunit divisibility condition")
    for record, (row, divisor) in zip(conditions, required_rows):
        if not isinstance(record, dict) or set(record) != {"row", "divisor", "terms"}:
            raise ValueError("Malformed divisibility condition")
        if (integer(record["row"], "condition row") != row or
                integer(record["divisor"], "condition divisor") != divisor):
            raise ValueError("Divisibility condition has the wrong Smith index or factor")
        if dense(record["terms"], rows, "image-condition vector") != supplied_left[row]:
            raise ValueError("Divisibility row differs from its certified row of U")
    if certificate.get("scope") != SCOPE:
        raise ValueError("Finite diagnostic scope label is absent or changed")
    return {
        "n": n, "matrix_shape": [rows, columns], "rank": rank,
        "array_kernel_rank": columns - rank, "line_dependency_rank": rows - rank,
        "nonunit_smith_factors": [value for value in diagonal if value > 1],
        "elementary_operations": len(certificate["smith"]["operations"]),
        "kernel_nonzero_coefficients": sum(len(record["terms"]) for record in kernel),
        "dependency_nonzero_coefficients": sum(len(record["terms"]) for record in dependencies),
        "U_nonzero_coefficients": sum(map(len, left_terms)),
        "V_nonzero_coefficients": sum(map(len, right_terms)),
        "status": "VERIFIED_FULL_INTEGER_KERNEL_DEPENDENCIES_AND_IMAGE",
        "scope": SCOPE,
    }


def image_membership(certificate, target, *, already_verified=False):
    """Evaluate the exact exported image conditions on an integer target."""
    if not already_verified:
        verify(certificate)
    if not isinstance(target, list) or len(target) != len(certificate["lines"]):
        raise ValueError("Wrong line-target length")
    if any(type(value) is not int for value in target):
        raise ValueError("Line targets must be exact integers")
    for record in certificate["line_dependency_basis"]:
        if sum(coefficient * target[index] for index, coefficient in record["terms"]):
            return False
    for record in certificate["image_criterion"]["divisibility"]:
        if sum(coefficient * target[index] for index, coefficient in record["terms"]) % record["divisor"]:
            return False
    return True


def inverse_left_action(vector, operations):
    """Apply U inverse using the reversed elementary row-operation log."""
    result = list(vector)
    for tag, *arguments in reversed(operations):
        if tag == "rs":
            i, j = arguments
            result[i], result[j] = result[j], result[i]
        elif tag == "ra":
            destination, source, multiplier = arguments
            result[destination] -= multiplier * result[source]
        elif tag == "rn":
            result[arguments[0]] *= -1
    return result


def negative_controls(certificate):
    """Each changed certificate must be rejected by the standalone verifier."""
    mutations = []

    def changed(label):
        copy = deepcopy(certificate)
        mutations.append((label, copy))
        return copy

    trial = changed("altered or fabricated array-kernel vector")
    if trial["array_kernel_basis"]:
        term = trial["array_kernel_basis"][0]["terms"][0]
        term[1] += 1 if term[1] > 0 else -1
    else:
        trial["array_kernel_basis"].append({"free_column": certificate["rank"], "terms": [[0, 1]]})
    trial = changed("altered line dependency")
    term = trial["line_dependency_basis"][0]["terms"][0]
    term[1] += 1 if term[1] > 0 else -1
    trial = changed("doubled dependency is not the certified integer basis")
    for term in trial["line_dependency_basis"][0]["terms"]:
        term[1] *= 2
    changed("omitted dependency vector")["line_dependency_basis"].pop()
    changed("omitted full signed line")["lines"].pop()
    trial = changed("misidentified full signed line")
    replacement = next(cell for cell in range(certificate["n"] ** 3) if cell not in trial["lines"][0])
    trial["lines"][0][-1] = replacement
    trial["lines"][0].sort()
    changed("nonunimodular elementary operation")["smith"]["operations"].append(["ra", 0, 0, 1])
    changed("altered diagonal preserving the divisibility chain")["smith"]["diagonal"][-1] *= 2
    trial = changed("altered exported left transformation")
    trial["left_transform_rows"][0][0][1] *= 2
    trial = changed("altered exported right transformation")
    trial["right_transform_columns"][0][0][1] *= 2
    trial = changed("altered image divisibility condition")
    trial["image_criterion"]["divisibility"][0]["divisor"] *= 2
    for label, trial in mutations:
        try:
            verify(trial)
        except ValueError:
            continue
        raise AssertionError(f"Corrupted certificate accepted: {label}")
    return [label for label, _ in mutations]


def self_test():
    outputs = []
    expected = {3: (27, 0, 22, [3, 3, 3, 6], 262),
                5: (89, 36, 20, [5, 5, 15], 1148)}
    input_directory = Path(__file__).resolve().parents[1] / "inputs"
    for n in (3, 5):
        certificate = produce(n)
        retained = json.loads((input_directory / f"signed_kernel_n{n}.json").read_text())
        if retained != certificate:
            raise AssertionError("Retained input differs from deterministic certificate production")
        summary = verify(retained)
        observed = (summary["rank"], summary["array_kernel_rank"], summary["line_dependency_rank"],
                    summary["nonunit_smith_factors"], summary["elementary_operations"])
        if observed != expected[n]:
            raise AssertionError("Unexpected exact small-order diagnostic")
        lines = retained["lines"]
        source = [cell % 7 - 3 for cell in range(n ** 3)]
        target = [sum(source[cell] for cell in line) for line in lines]
        assert image_membership(retained, target, already_verified=True)
        # Every nonunit row supplies a rationally compatible integer vector
        # violating that divisibility condition, and a multiple that lifts.
        rank = retained["rank"]
        for record in retained["image_criterion"]["divisibility"]:
            transformed = [0] * len(lines)
            transformed[record["row"]] = 1
            obstruction = inverse_left_action(transformed, retained["smith"]["operations"])
            assert all(sum(coefficient * obstruction[index] for index, coefficient in dependency["terms"]) == 0
                       for dependency in retained["line_dependency_basis"])
            assert not image_membership(retained, obstruction, already_verified=True)
            attainable = [record["divisor"] * value for value in obstruction]
            assert image_membership(retained, attainable, already_verified=True)
            column = dense(retained["right_transform_columns"][record["row"]], n ** 3, "witness column")
            assert [sum(column[cell] for cell in line) for line in lines] == attainable
        transformed = [0] * len(lines)
        transformed[rank] = 1
        bad_relation = inverse_left_action(transformed, retained["smith"]["operations"])
        assert not image_membership(retained, bad_relation, already_verified=True)
        summary["negative_controls_rejected"] = negative_controls(retained)
        summary["retained_input"] = f"signed_kernel_n{n}.json"
        summary["image_membership_controls"] = 2 + 2 * len(retained["image_criterion"]["divisibility"])
        outputs.append(summary)
    return {"certificates": outputs, "scope": SCOPE}


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--certificate", action="store_true", help="emit a compact full certificate")
    mode.add_argument("--verify", type=Path, metavar="FILE", help="verify an independently supplied certificate")
    mode.add_argument("--self-test", action="store_true", help="reproduce retained certificates and run controls (default)")
    parser.add_argument("--n", type=int, choices=(3, 5), default=3)
    args = parser.parse_args()
    if args.certificate:
        certificate = produce(args.n)
        verify(certificate)
        print(json.dumps(certificate, separators=(",", ":")))
    elif args.verify:
        print(json.dumps(verify(json.loads(args.verify.read_text())), indent=2))
    else:
        print(json.dumps(self_test(), indent=2))


if __name__ == "__main__":
    main()
