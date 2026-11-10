#!/usr/bin/env python3
"""Independent bounded comparison with the exact pinned PA926 source.

No random sampling, external services, or source mutations. This script checks
192 raw matrix/environment cases, 64 postfix certificates, and (with --axioms)
144 selector/parameter cases. It does not prove unbounded source correspondence.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="pinned Lake executable")
    parser.add_argument("--axioms", action="store_true", help="also evaluate all nine axiom branches")
    args = parser.parse_args()
    # The explicitly bounded nested-pair axiom vectors contain integers with
    # more than Python's default 4,300 decimal digits. No untrusted input is read.
    sys.set_int_max_str_digits(100_000)
    root = Path(__file__).resolve().parents[1]
    source = root / "bindings/pa926/producer.py"
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    if digest != "715bcfe1704f372bf3bdc436eee798501a780d50fe3028d52e0a0129b58c7247":
        raise RuntimeError(f"Unexpected source SHA-256: {digest}")
    spec = importlib.util.spec_from_file_location("pa926_review_source", source)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    command = [args.lake, "env", "lean", "--run", "PASoundness/ReferenceVectors.lean"]
    if args.axioms:
        command.append("--axioms")
    with tempfile.TemporaryFile(mode="w+b") as errors:
        result = subprocess.run(command, cwd=root / "lean", stdout=subprocess.PIPE,
                                stderr=errors, timeout=120, check=False)
        if result.returncode:
            errors.seek(0, 2)
            size = errors.tell()
            errors.seek(max(0, size - 4096))
            tail = errors.read().decode("utf-8", "replace")
            raise RuntimeError(f"Lean vectors exited {result.returncode}; stderr tail:\n{tail}")
    lines = result.stdout.decode("utf-8").strip().splitlines()
    expected_lines = 5 if args.axioms else 4
    if len(lines) != expected_lines:
        raise RuntimeError(f"Expected {expected_lines} JSON vector lines; got {len(lines)}")
    observed = [json.loads(line) for line in lines]

    # Both environment encodings deliberately use the literal pairing source.
    # The last is newest name-0=0 over earlier name-0=1, testing shadowing.
    name0_one = module.pair(module.pair(0, 1), 0)
    name0_shadow = module.pair(module.pair(0, 0), name0_one)
    for index, environment in enumerate([0, name0_one, name0_shadow]):
        expected = []
        for code in range(64):
            valid, truth = module.matrix(code, environment)
            expected.append(truth if valid else 2)
        if observed[index] != expected:
            raise AssertionError(f"Matrix vector mismatch, environment index {index}")
    if observed[3] != [module.theorem(code) for code in range(64)]:
        raise AssertionError("Postfix theorem vector mismatch")
    if args.axioms:
        expected = [module.axiom(selector, *values)
                    for selector in range(9)
                    for values in itertools.product(range(2), repeat=4)]
        if observed[4] != expected:
            raise AssertionError("Axiom vector mismatch")
    print(json.dumps({"source_sha256": digest, "matrix_codes": [0, 63],
                      "matrix_environments": [0, name0_one, name0_shadow],
                      "matrix_cases": 192, "postfix_certificates": [0, 63],
                      "postfix_cases": 64, "axiom_cases": 144 if args.axioms else 0,
                      "all_equal": True}, sort_keys=True))


if __name__ == "__main__":
    main()
