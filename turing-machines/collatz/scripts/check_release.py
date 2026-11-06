#!/usr/bin/env python3
"""Validate canonical source identities, original module names, and exact tables."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def verify():
    manifest = json.loads((ROOT / "PROVENANCE.json").read_text())
    expected = manifest["lean_sources"]
    layout = manifest["lean_source_paths"]
    require(set(expected) == set(layout), "Source inventory and layout differ")
    require(len(expected) == 22, "Expected all 22 audited Lean sources")
    actual = {str(p.relative_to(ROOT))
              for folder in ("evaluator12/proofs", "cycle16/proofs", "shared/proofs")
              for p in (ROOT / folder).glob("*.lean")}
    require(actual == set(layout.values()), "Canonical Lean source inventory differs")
    imports = json.loads((ROOT / "proofs/IMPORTS.json").read_text())
    require(set(imports) == set(expected), "Import inventory differs")
    for name, digest in expected.items():
        data = (ROOT / layout[name]).read_bytes()
        require(hashlib.sha256(data).hexdigest() == digest, "Source hash differs: " + name)
        declared = re.findall(r"^import ([^\n]+)", data.decode(), re.MULTILINE)
        require(declared == imports[name], "Imports differ: " + name)
        for group in declared:
            for module in group.split():
                require(module == "Lean" or module.replace(".", "/") + ".lean" in layout,
                        "Unmapped module: " + module)
    for count, item in manifest["machines"].items():
        data = (ROOT / item["file"]).read_bytes()
        require(hashlib.sha256(data).hexdigest() == item["file_sha256"], item["file"])
        table = data.decode().rstrip("\n")
        require(table == item["string"], "Machine string differs: " + count)
        require(hashlib.sha256(table.encode()).hexdigest() == item["string_sha256"], count)
        source = (ROOT / layout["CollatzTM/Machine" + count + ".lean"]).read_text()
        literal = source.split('def tableString : String := "')[1].split('"')[0]
        require(table == literal, "Lean machine table differs: " + count)
        require(len(table.split("_")) == int(count), "State count differs: " + count)
        compatibility = ROOT.parent / "machines" / Path(item["file"]).name
        require(compatibility.read_bytes() == data, "Compatibility table differs: " + count)
        package = ROOT / Path(item["file"]).parent
        local = json.loads((package / "PROVENANCE.json").read_text())
        require(local["machine"] == dict(item, file=Path(item["file"]).name),
                "Local machine provenance differs: " + count)
        for path, identity in local["machine_specific_lean_sources"].items():
            require(layout[identity["lean_module_path"]] ==
                    str((package / path).relative_to(ROOT)), "Local source path differs")
            require(identity["sha256"] == expected[identity["lean_module_path"]],
                    "Local source digest differs")
    require((ROOT / "proofs/lean-toolchain").read_text().strip() == manifest["toolchain"],
            "Toolchain differs")
    require(json.loads((ROOT / "proofs/lake-manifest.json").read_text())["packages"] == [],
            "Unexpected third-party package")
    beeper = ROOT / "beeping17"
    source = json.loads((beeper / "SOURCE.json").read_text())
    for name, identity in source["files"].items():
        require(hashlib.sha256((beeper / name).read_bytes()).hexdigest() ==
                identity["published_sha256"], "Beeper source hash differs: " + name)
    print("Verified 22 exact Lean sources, module/import mapping, three exact tables, "
          "local provenance, beeper source hashes, compatibility copies and toolchain.")
    return manifest

if __name__ == "__main__":
    verify()
