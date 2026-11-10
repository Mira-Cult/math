#!/usr/bin/env python3
"""Verify copied source identities and the PA926 table's finite structure.

This checker never executes the machine or its producer. Hashes and finite-row
validation are identity/shape evidence, not an execution-refinement theorem.
The optional Git-object replay uses already-local objects and forbids fetching.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


TABLE_SHA256 = "2358b4847410f8ec69d0b51d7e7fe93fb5aa1c47877a650de8bd2d9b82356969"
ORIGINS = {
    "bindings/pa926/machine.tm": (
        "eedb98409a6c64f9d89bed774cd763f6702ca84c",
        "problems/omega-arithmetical-soundness/recovery/pa-successor/machines/compact-direct-boot/quotient/machine.tm"),
    "bindings/pa926/producer.py": (
        "eedb98409a6c64f9d89bed774cd763f6702ca84c",
        "problems/omega-arithmetical-soundness/recovery/pa-successor/code/compact/source.py"),
    "bindings/pa926/trace_semantics.py": (
        "eedb98409a6c64f9d89bed774cd763f6702ca84c",
        "problems/omega-arithmetical-soundness/recovery/pa-successor/code/trace_semantics.py"),
    "bindings/predecessor/OmegaSoundnessInterface.lean.txt": (
        "50930a28d1f2d9b6f88170beb0c343307ed64fec",
        "problems/pa-full-soundness/formal/OmegaSoundnessInterface.lean"),
    "lean/Shared/Beeping/Events.lean": (
        "bd891a9e27c73103b3ce76b61617585ab82382ac", "Shared/Beeping/Events.lean"),
    "lean/Shared/Beeping/Machines.lean": (
        "bd891a9e27c73103b3ce76b61617585ab82382ac", "Shared/Beeping/Machines.lean"),
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def git_blob(data: bytes) -> str:
    header = f"blob {len(data)}\0".encode("ascii")
    return hashlib.sha1(header + data).hexdigest()


def check_table(data: bytes) -> dict:
    require(hashlib.sha256(data).hexdigest() == TABLE_SHA256, "Wrong selected PA926 table")
    require(data.endswith(b"\n") and b"\r" not in data, "Noncanonical table line endings")
    lines = data.decode("ascii").splitlines()
    required_header = ["#! format bit-events-v1", "#! states 926", "#! start 0",
                       "#! blank 0", "#! head 0"]
    require(lines[:5] == required_header, "Unexpected table hardware/event convention")
    rows = lines[5:]
    require(len(rows) == 1852, "Expected exactly 1,852 transition rows")
    observed_events = {}
    for index, line in enumerate(rows):
        fields = line.split()
        require(len(fields) == 6, f"Malformed table row {index}")
        state, read, write, move, next_state, event = fields
        require(all(re.fullmatch(r"0|[1-9][0-9]*", x) for x in [state, read, write, next_state]),
                f"Nonnatural or noncanonical numeric field in row {index}")
        q, symbol, written, destination = map(int, [state, read, write, next_state])
        require((q, symbol) == divmod(index, 2), f"Duplicate, omitted, or reordered row {index}")
        require(written in (0, 1), f"Nonbinary write in row {index}")
        require(move in ("L", "R"), f"Nonstandard move in row {index}")
        require(0 <= destination < 926, f"Out-of-range destination in row {index}")
        require(event in ("-", "0", "1"), f"Malformed event label in row {index}")
        if event != "-":
            observed_events[(q, symbol)] = int(event)
    require(observed_events == {(198, 1): 0, (199, 1): 1}, "Incorrect BIT0/BIT1 row map")
    return {"states": 926, "rows": 1852, "start": 0, "head": 0, "blank": 0,
            "events": [{"state": q, "read": r, "bit": b}
                       for (q, r), b in sorted(observed_events.items())],
            "sha256": TABLE_SHA256}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--git-object-check", action="store_true",
                        help="also compare to already-local exact upstream commit:path blobs")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / "bindings/manifest.json").read_text(encoding="utf-8"))
    require(manifest.get("schema") == 1, "Unexpected binding manifest schema")
    entries = manifest.get("files")
    require(isinstance(entries, list) and len(entries) == len(ORIGINS), "Unexpected binding inventory")
    require({entry.get("path") for entry in entries} == set(ORIGINS), "Changed/duplicate binding paths")
    total_bytes = 0
    table = None
    environment = os.environ.copy()
    environment.update(GIT_NO_LAZY_FETCH="1", GIT_TERMINAL_PROMPT="0")
    for entry in entries:
        relative = entry["path"]
        path = root / relative
        require(path.is_file() and not path.is_symlink(), f"Missing/nonregular binding: {relative}")
        require(path.resolve().is_relative_to(root), f"Binding escapes lane: {relative}")
        require(entry.get("repository") == "Mira-Cult/math-wip", f"Wrong origin repository: {relative}")
        require((entry.get("commit"), entry.get("source_path")) == ORIGINS[relative],
                f"Wrong pinned origin: {relative}")
        data = path.read_bytes()
        require(len(data) == entry["bytes"], f"Byte-count mismatch: {relative}")
        require(hashlib.sha256(data).hexdigest() == entry["sha256"], f"SHA-256 mismatch: {relative}")
        require(git_blob(data) == entry["git_blob"], f"Git blob mismatch: {relative}")
        total_bytes += len(data)
        if args.git_object_check:
            identity = f"{entry['commit']}:{entry['source_path']}"
            result = subprocess.run(["git", "-c", "protocol.allow=never", "cat-file", "blob", identity],
                                    cwd=root.parents[1], env=environment, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE, check=False)
            require(result.returncode == 0,
                    f"Local origin object unavailable: {identity}; no network fetch attempted")
            require(result.stdout == data, f"Upstream Git-object mismatch: {relative}")
        if relative == "bindings/pa926/machine.tm":
            table = check_table(data)
    print(json.dumps({"bindings": len(entries), "bytes": total_bytes,
                      "local_origin_objects_replayed": args.git_object_check,
                      "pa926": table, "scope": "identity and finite structure only"}, sort_keys=True))


if __name__ == "__main__":
    main()
