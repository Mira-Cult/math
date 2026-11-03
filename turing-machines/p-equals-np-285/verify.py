#!/usr/bin/env python3
"""Independent public-packet integrity checks, not a mathematical proof checker."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
FORMAL = ROOT / "formalization"
MARKED_HASH = "1aeafb43c7a9a8f599476ea23bbb5723506d33ca26e5186771fb942a88ad19d7"
COMPANION_HASH = "12fba54d7e9c51ca6e149ae4103a3753378a7cff7cfb3e66bcda19804bfeb880"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def table(path: Path, states: int, marked: bool, digest: str) -> list[tuple]:
    raw = path.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == digest, f"Wrong SHA-256: {path}")
    header = {}
    rows = []
    for line in raw.decode("ascii").splitlines():
        if line.startswith("#! "):
            key, value = line[3:].split(maxsplit=1)
            require(key not in header, f"Duplicate header: {key}")
            header[key] = value
        elif line and not line.startswith("#"):
            fields = line.split()
            require(len(fields) == (6 if marked else 5), "Wrong row width")
            q, read, write, direction, target = fields[:5]
            row = (int(q), int(read), int(write), direction, int(target))
            if marked:
                row += (int(fields[5]),)
            rows.append(row)
    for key, value in {"states": str(states), "start": "0", "blank": "0", "head": "0"}.items():
        require(header.get(key) == value, f"Wrong {key} header")
    require(header.get("format") == ("beeper-events-v1" if marked else "beeper-v1"), "Wrong format")
    if not marked:
        require(header.get("beep") == "1", "Wrong companion observer")
    require(len(rows) == states * 2, "Wrong row count")
    for index, row in enumerate(rows):
        q, read, write, direction, target = row[:5]
        require((q, read) == divmod(index, 2), "Wrong row order or duplicate row")
        require(write in (0, 1) and direction in ("L", "R") and 0 <= target < states,
                "Invalid transition")
        if marked:
            require(row[5] in (0, 1), "Invalid event flag")
    if marked:
        require([r for r in rows if r[5]] == [(121, 1, 0, "L", 1, 1)], "Wrong event mask")
    return rows


def main() -> None:
    table(ROOT / "events.tm", 285, True, MARKED_HASH)
    table(ROOT / "companion.tm", 286, False, COMPANION_HASH)
    for name in ("events.tm", "companion.tm"):
        require((ROOT / name).read_bytes() == (FORMAL / "Shared/PNP/Record285" / name).read_bytes(),
                f"Display and embedded literal differ: {name}")

    inventory = json.loads((ROOT / "SOURCE-MANIFEST.json").read_text())
    for item in inventory["files"]:
        path = ROOT / item["public_path"]
        raw = path.read_bytes()
        require(len(raw) == item["bytes"], f"Wrong length: {path}")
        require(hashlib.sha256(raw).hexdigest() == item["sha256"], f"Wrong digest: {path}")
        blob = hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()
        require(blob == item["upstream_git_blob"], f"Wrong upstream Git blob: {path}")

    local_imports = 0
    external_imports = set()
    for path in FORMAL.rglob("*.lean"):
        if ".lake" in path.parts:
            continue
        source = path.read_text()
        for match in re.finditer(r"^\s*(?:public\s+)?import\s+([^\n]+)", source, re.M):
            for name in match[1].split():
                if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", name):
                    continue
                if name.startswith("Shared."):
                    local_imports += 1
                    target = FORMAL / (name.replace(".", "/") + ".lean")
                    require(target.is_file(), f"Missing local import: {name}")
                else:
                    external_imports.add(name)
        for included in re.findall(r'include_str\s+"([^"]+)"', source):
            require((path.parent / included).is_file(), f"Missing include: {included}")
    manifest = json.loads((FORMAL / "lake-manifest.json").read_text())
    require(len(manifest["packages"]) == 10, "Unexpected lockfile package count")
    require(all(p["url"].startswith("https://github.com/") for p in manifest["packages"]),
            "Non-public dependency URL")
    print(f"PASS: 570 marked rows, 572 companion rows, unique event, exact literal copies")
    print(f"PASS: {len(inventory['files'])} unchanged upstream source/input files")
    print(f"PASS: {local_imports} local import edges and literal includes resolve")
    print(f"External imports: {', '.join(sorted(external_imports))}")
    print("Integrity checks are not kernel checking or mathematical review.")


if __name__ == "__main__":
    main()
