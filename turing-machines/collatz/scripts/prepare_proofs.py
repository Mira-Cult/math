#!/usr/bin/env python3
"""Assemble the original Lean module layout from byte-identical canonical sources."""
import argparse
from pathlib import Path
import shutil
import subprocess
from check_release import ROOT, verify

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="run lake build after assembly")
    parser.add_argument("--audit", action="store_true", help="build, then print theorem/axiom audit")
    parser.add_argument("--kernel", action="store_true", help="build, then freshly recheck the kernel")
    args = parser.parse_args()
    manifest = verify()
    destination = ROOT / ".build" / "lean"
    destination.mkdir(parents=True, exist_ok=True)
    expected = set(manifest["lean_source_paths"])
    # Only remove obsolete generated Lean sources, never canonical research files.
    for path in destination.rglob("*.lean"):
        if ".lake" not in path.relative_to(destination).parts:
            if str(path.relative_to(destination)) not in expected:
                path.unlink()
    for module_path, canonical_path in manifest["lean_source_paths"].items():
        target = destination / module_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / canonical_path, target)
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "IMPORTS.json"):
        shutil.copyfile(ROOT / "proofs" / name, destination / name)
    print("Prepared exact 22-file Lean workspace: " + str(destination), flush=True)
    if args.build or args.audit or args.kernel:
        subprocess.run(["lake", "build"], cwd=destination, check=True)
    if args.audit:
        subprocess.run(["lake", "env", "lean", "Audit.lean"], cwd=destination, check=True)
    if args.kernel:
        subprocess.run(["lake", "env", "leanchecker", "--fresh", "CollatzTM"],
                       cwd=destination, check=True)

if __name__ == "__main__":
    main()
