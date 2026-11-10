#!/usr/bin/env python3
"""Check recovered PA804 identities, literal rows and the unchanged record input.

This is finite artifact verification, not a Lean execution/refinement theorem.
It does not execute the producer, regenerate a machine or contact a service.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

from verify_bindings import git_blob, require


ARCHIVE_SHA256 = "b1cb4f1fdbcc5e183a049c2e57adcfa1b28df80e91c0962301b6f1388601f9e9"
TABLE_SHA256 = "ba5ecf486757f55aa872d1a10fc5360cbed2070cde2d975fa2ee1c54fc536df8"
SOURCE_SHA256 = "715bcfe1704f372bf3bdc436eee798501a780d50fe3028d52e0a0129b58c7247"


def main() -> None:
    lane = Path(__file__).resolve().parents[1]
    root = lane / "bindings/pa804"
    origin = json.loads((root / "origin.json").read_text())
    require(origin.get("schema") == 1, "Unexpected successor manifest schema")
    require(origin["archive"]["sha256"] == ARCHIVE_SHA256, "Wrong recovered archive")
    entries = origin["files"]
    require(len(entries) == 16, "Unexpected retained source/data inventory")
    require(len({e["path"] for e in entries}) == len(entries), "Duplicate binding")
    for entry in entries:
        path = root / entry["path"]
        require(path.is_file() and not path.is_symlink(), f"Missing/nonregular binding: {path}")
        require(path.resolve().is_relative_to(root), "Binding escapes successor directory")
        data = path.read_bytes()
        require(len(data) == entry["bytes"], f"Wrong byte count: {path}")
        require(hashlib.sha256(data).hexdigest() == entry["sha256"], f"Wrong SHA256: {path}")
        require(git_blob(data) == entry["git_blob"], f"Wrong Git blob: {path}")

    inputs = json.loads((root / "input-manifest.json").read_text())
    require(len(inputs) == 10, "Unexpected selected build-input inventory")
    indexed = {entry["path"]: entry for entry in entries}
    for path, digest in inputs.items():
        require(path in indexed and indexed[path]["sha256"] == digest,
                f"Selected input differs from recovered manifest: {path}")
    source = (root / "baseline/code/compact/source.py").read_bytes()
    require(hashlib.sha256(source).hexdigest() == SOURCE_SHA256, "Wrong compact reference source")
    require(source == (lane / "bindings/pa926/producer.py").read_bytes(),
            "PA804 reference record input differs from pinned PA926")

    data = (root / "machine.tm").read_bytes()
    require(hashlib.sha256(data).hexdigest() == TABLE_SHA256, "Wrong selected PA804 table")
    require(data.endswith(b"\n") and b"\r" not in data, "Noncanonical line endings")
    lines = data.decode("ascii").splitlines()
    require(lines[:5] == ["#! format bit-events-v1", "#! states 804", "#! start 0",
                           "#! blank 0", "#! head 0"], "Wrong hardware convention")
    require(len(lines[5:]) == 1608, "Expected exactly 1,608 transition rows")
    events = {}
    for index, line in enumerate(lines[5:]):
        fields = line.split()
        require(len(fields) == 6, f"Malformed row {index}")
        state, read, write, move, target, event = fields
        require(all(re.fullmatch(r"0|[1-9][0-9]*", s) for s in [state, read, write, target]),
                f"Noncanonical numeric field in row {index}")
        q, symbol, written, destination = map(int, [state, read, write, target])
        require((q, symbol) == divmod(index, 2), f"Wrong/duplicate/missing row {index}")
        require(written in (0, 1) and move in ("L", "R") and 0 <= destination < 804,
                f"Invalid physical transition {index}")
        require(event in ("-", "0", "1"), f"Invalid event in row {index}")
        if event != "-":
            events[q, symbol] = int(event)
    require(events == {(174, 1): 0, (175, 1): 1}, "Wrong PA804 exit-event map")
    declared = origin["machine"]
    require(declared == {
        "states": 804, "rows": 1608, "start": 0, "head": 0, "blank": 0,
        "events": [{"state": 174, "read": 1, "bit": 0},
                   {"state": 175, "read": 1, "bit": 1}],
        "event_timing": "exit row", "sha256": TABLE_SHA256}, "Wrong declared hardware identity")
    metadata = json.loads((root / "metadata.json").read_text())
    require(metadata["variant"] == "ReassociatedOneStack", "Wrong selected implementation")
    require(metadata["table_sha256"] == TABLE_SHA256 and metadata["source_sha256"] == SOURCE_SHA256,
            "Metadata points at different table or reference source")
    print(json.dumps({"retained_bindings": len(entries), "states": 804, "rows": 1608,
                      "sha256": TABLE_SHA256, "same_reference_record_source": True,
                      "events": declared["events"],
                      "scope": "identity and finite structure only"}, sort_keys=True))


if __name__ == "__main__":
    main()
