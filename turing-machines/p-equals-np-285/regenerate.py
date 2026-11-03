#!/usr/bin/env python3
"""Regenerate untrusted certificate sources in an isolated temporary copy."""
import hashlib
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "formalization/Shared/PNP/Record285"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


with tempfile.TemporaryDirectory(prefix="pnp285-certificates-") as temp:
    target = Path(temp) / "Record285"
    shutil.copytree(SOURCE, target, ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
    before = {p.relative_to(target): digest(p) for p in target.rglob("*.lean")}
    scripts = sorted(target.glob("generate_*.py"))
    for script in scripts:
        print(f"Running {script.name}", flush=True)
        subprocess.run([sys.executable, "-B", str(script)], check=True, cwd=target)
    subprocess.run([sys.executable, "-B", str(target / "generate_projection_grammar.py"),
                    "--pre-control"], check=True, cwd=target)
    changed = [str(path) for path, h in before.items() if digest(target / path) != h]
    added = sorted(str(p.relative_to(target)) for p in target.rglob("*.lean")
                   if p.relative_to(target) not in before)
    if changed or added:
        raise SystemExit(f"Certificate-source mismatch: changed={changed}, added={added}")
    print(f"PASS: {len(scripts)} generators plus pre-control variant; all Lean sources unchanged")
    print("Regeneration is provenance checking, not kernel checking or a compiler-correctness proof.")
