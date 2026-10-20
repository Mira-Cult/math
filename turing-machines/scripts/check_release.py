#!/usr/bin/env python3
"""Check public release identities and imports without executing machine code."""
import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent
proofs = root / "proofs"
manifest = json.loads((root / "PROVENANCE.json").read_text())
lean_sources = manifest["lean_sources"]
actual = {str(p.relative_to(proofs)) for p in proofs.rglob("*.lean")
          if ".lake" not in p.parts and ".build" not in p.parts}
assert actual == set(lean_sources), "Lean source inventory differs"
assert len(actual) == 22, "Expected all 22 audited Lean source files"
imports = json.loads((proofs / "IMPORTS.json").read_text())
for name, digest in lean_sources.items():
    data = (proofs / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == digest, name
    declared = re.findall(r"^import ([^\n]+)", data.decode(), re.MULTILINE)
    assert declared == imports[name], "Import inventory mismatch: " + name
    for group in declared:
        for module in group.split():
            if module == "Lean":
                continue
            assert (proofs / (module.replace(".", "/") + ".lean")).is_file(), module
for count, item in manifest["machines"].items():
    data = (root / item["file"]).read_bytes()
    assert hashlib.sha256(data).hexdigest() == item["file_sha256"], item["file"]
    table = data.decode().rstrip("\n")
    assert table == item["string"], item["file"]
    assert hashlib.sha256(table.encode()).hexdigest() == item["string_sha256"], count
    source = (proofs / ("CollatzTM/Machine" + count + ".lean")).read_text()
    compiled_string = source.split('def tableString : String := "')[1].split('"')[0]
    assert table == compiled_string, "Machine table differs: " + count
    assert len(table.split("_")) == int(count), count
assert (proofs / "lean-toolchain").read_text().strip() == manifest["toolchain"]
assert json.loads((proofs / "lake-manifest.json").read_text())["packages"] == []
print("Verified all 22 audited Lean sources, imports, exact .tm tables and pinned toolchain.")
