#!/usr/bin/env python3
"""Compile and audit all project Lean modules, separately from check.py.

Allow only Lean's standard classical logic, propositional extensionality, and
quotient soundness axioms. This rejects sorryAx, native_decide's ofReduceBool,
and any custom axiom even when imported transitively by a project declaration.
The negative probe is a temporary module, not part of the research package.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
ROOT_NAMES = ("Shared", "ComplexityBridge", "PNP", "NPCONP", "MachineBindings")
ALLOWED = ("propext", "Classical.choice", "Quot.sound")
CANONICAL_MODULE = "FormalConjecturesForMathlib.Computability.Complexity"
PROBE_MODULE = "AxiomGateProbe"
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
SERIAL_SHARD = re.compile(
    r"(?:Shared\.Beeping\.NPcoNP\.Parent290(?:Mask|Ownership)Shard[0-9]+"
    r"|Shared\.Beeping\.NPcoNP\.(?:GrammarFullRows|GraphCandidate284)Shard[0-9]+"
    r"|Shared\.Beeping\.NPcoNP\.Grammar284Contract(?:Target|Output)Shard[0-9]+"
    r"|Shared\.Beeping\.NPcoNP\.Grammar284Source(?:Chars|Tails)"
    r"|Shared\.Beeping\.NPcoNP\.GrammarSourceNodeShard[0-9]+"
    r"|Shared\.Beeping\.NPcoNP\.Table284Source(?:Chars|Join|Clean|Split|Lines)"
    r"|Shared\.Beeping\.NPcoNP\.Table284LineData"
    r"|Shared\.Beeping\.NPcoNP\.Table284CleanShard[0-9]+"
    r"|Shared\.Beeping\.NPcoNP\.Table284RowShard[0-9]+"
    r"|Shared\.Beeping\.NPcoNP\.Table284LiteralBinding"
    r"|Shared\.Beeping\.NPcoNP\.Table285(?:Exit)?Source(?:Chars|Join|Clean|Split)"
    r"|Shared\.Beeping\.NPcoNP\.Table285(?:Exit)?LineData"
    r"|Shared\.Beeping\.NPcoNP\.Table285(?:Exit)?(?:Clean|Row)Shard[0-9]+"
    r"|Shared\.Beeping\.NPcoNP\.Table285(?:Exit)?LiteralBinding"
    r"|Shared\.Beeping\.NPcoNP\.EventQuotient285Shard[0-9]+"
    r"|Shared\.Beeping\.NPcoNP\.ExpansionTrace\.(?:Paths|Stage[0-9]+|Final))\Z"
)


def modules() -> list[str]:
    # Fail closed if a new project Lean source is placed outside the audited
    # library roots; otherwise a future endpoint could silently evade the gate.
    for directory, subdirs, files in os.walk(ROOT, followlinks=False):
        subdirs[:] = [name for name in subdirs if name not in {".git", ".lake", "__pycache__"}]
        for name in subdirs:
            if (Path(directory) / name).is_symlink():
                raise RuntimeError(f"refusing symlinked source directory: {Path(directory) / name}")
        for filename in files:
            if not filename.endswith(".lean"):
                continue
            path = Path(directory) / filename
            relative = path.relative_to(ROOT)
            root_name = relative.parts[0] if len(relative.parts) > 1 else path.stem
            if root_name not in ROOT_NAMES:
                raise RuntimeError(f"Lean source outside audited roots: {relative}")
    found: set[str] = set()
    for root_name in ROOT_NAMES:
        root_file = ROOT / f"{root_name}.lean"
        root_dir = ROOT / root_name
        paths = ([root_file] if root_file.is_file() else [])
        if root_dir.is_dir():
            paths += list(root_dir.rglob("*.lean"))
        for path in paths:
            if path.is_symlink():
                raise RuntimeError(f"refusing symlinked Lean source: {path}")
            parts = path.relative_to(ROOT).with_suffix("").parts
            if not all(NAME.fullmatch(part) for part in parts):
                raise RuntimeError(f"invalid Lean module path: {path}")
            found.add(".".join(parts))
    if not found or "Shared" not in found:
        raise RuntimeError("no Shared root module found")
    return sorted(found)


def gate_source(imports: list[str], extra_roots: tuple[str, ...] = ()) -> str:
    roots = ", ".join(f"`{name}" for name in (*ROOT_NAMES, *extra_roots))
    allowed = ", ".join(f"`{name}" for name in ALLOWED)
    return ("import Lean\n" + "".join(f"import {name}\n" for name in imports) + f"""
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let roots : Array Name := #[{roots}]
  let allowed : Array Name := #[{allowed}]
  let mut checked : Nat := 0
  let mut failures : Array (Name × Name) := #[]
  for (decl, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? decl then
      let owner := modules[idx.toNat]!
      if roots.contains owner.getRoot then
        checked := checked + 1
        let axioms ← collectAxioms decl
        for ax in axioms do
          unless allowed.contains ax do
            failures := failures.push (decl, ax)
  if checked == 0 then
    throwError "axiom gate examined no project declarations"
  let canonical : Array Name := #[`ComplexityTheory.DecisionProblem,
    `ComplexityTheory.IsPolyTimeWithEncoding, `ComplexityTheory.IsPolyTime,
    `ComplexityTheory.P, `ComplexityTheory.NP, `ComplexityTheory.coNP,
    `BitstringEncoding.bitEncode, `BitstringEncoding.bitDecode]
  for decl in canonical do
    if (env.find? decl).isNone then
      throwError m!"required canonical declaration not found: {{decl}}"
    checked := checked + 1
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        failures := failures.push (decl, ax)
  if !failures.isEmpty then
    throwError m!"disallowed axiom dependencies (declaration, axiom): {{failures.toList}}"
  logInfo m!"axiom gate accepted {{checked}} project declarations"
""")


def negative_probe_source() -> str:
    # Exercise exactly the same checker on the probe and on the required
    # canonical declarations. Importing every project module here would audit
    # the entire project twice; the final gate below still imports every one.
    return gate_source([CANONICAL_MODULE, PROBE_MODULE], (PROBE_MODULE,))


def serial_order(name: str) -> tuple[int, int, int, str]:
    """Build prerequisite certificate families before dependent shards."""
    prefix = "Shared.Beeping.NPcoNP.ExpansionTrace."
    family = name.removeprefix("Shared.Beeping.NPcoNP.")
    if family.startswith("Parent290MaskShard"):
        return (0, 0, 0, name)
    if family.startswith("Parent290OwnershipShard"):
        return (1, 0, 0, name)
    if name.startswith(prefix):
        leaf = name.removeprefix(prefix)
        if leaf == "Paths":
            return (2, 0, 0, name)
        if leaf == "Final":
            return (2, 2, 0, name)
        return (2, 1, int(leaf.removeprefix("Stage")), name)
    if family.startswith("GrammarFullRowsShard"):
        return (3, 0, 0, name)
    if family.startswith("GraphCandidate284Shard"):
        return (4, 0, 0, name)
    if family.startswith("Grammar284ContractTargetShard"):
        return (5, 0, 0, name)
    if family.startswith("Grammar284ContractOutputShard"):
        return (6, 0, 0, name)
    if family == "Grammar284SourceChars":
        return (7, 0, 0, name)
    if family == "Grammar284SourceTails":
        return (7, 1, 0, name)
    if family.startswith("GrammarSourceNodeShard"):
        return (8, 0, 0, name)
    if family == "Table284SourceChars":
        return (9, 0, 0, name)
    if family == "Table284LineData":
        return (9, 1, 0, name)
    if family == "Table284SourceJoin":
        return (9, 2, 0, name)
    if family.startswith("Table284CleanShard"):
        return (9, 3, 0, name)
    if family == "Table284SourceClean":
        return (9, 4, 0, name)
    if family == "Table284SourceSplit":
        return (9, 5, 0, name)
    if family == "Table284SourceLines":
        return (9, 6, 0, name)
    if family.startswith("Table284RowShard"):
        return (10, 0, 0, name)
    if family == "Table284LiteralBinding":
        return (11, 0, 0, name)
    if family == "Table285SourceChars":
        return (12, 0, 0, name)
    if family == "Table285LineData":
        return (12, 1, 0, name)
    if family == "Table285SourceJoin":
        return (12, 2, 0, name)
    if family.startswith("Table285CleanShard"):
        return (12, 3, 0, name)
    if family == "Table285SourceClean":
        return (12, 4, 0, name)
    if family == "Table285SourceSplit":
        return (12, 5, 0, name)
    if family.startswith("Table285RowShard"):
        return (13, 0, 0, name)
    if family == "Table285LiteralBinding":
        return (14, 0, 0, name)
    # Also serialize any preserved Exit-prefixed work in a live workspace;
    # inclusion here does not select it as the canonical table binding.
    if family == "Table285ExitSourceChars":
        return (15, 0, 0, name)
    if family == "Table285ExitLineData":
        return (15, 1, 0, name)
    if family == "Table285ExitSourceJoin":
        return (15, 2, 0, name)
    if family.startswith("Table285ExitCleanShard"):
        return (15, 3, 0, name)
    if family == "Table285ExitSourceClean":
        return (15, 4, 0, name)
    if family == "Table285ExitSourceSplit":
        return (15, 5, 0, name)
    if family.startswith("Table285ExitRowShard"):
        return (16, 0, 0, name)
    if family == "Table285ExitLiteralBinding":
        return (17, 0, 0, name)
    # Callers use this key only on SERIAL_SHARD matches.
    return (18, 0, 0, name)


def build_modules(project_modules: list[str]) -> None:
    # Each certificate shard performs an unusually large kernel reduction.
    # Build them serially so the aggregate build can reuse their results
    # without scheduling all of them concurrently on a constrained runner.
    # Every discovered module is still included in the final build and audit.
    serial = (name for name in project_modules if SERIAL_SHARD.fullmatch(name))
    for name in sorted(serial, key=serial_order):
        subprocess.run(["lake", "build", f"+{name}"], check=True)
    subprocess.run(["lake", "build", *[f"+{name}" for name in project_modules]], check=True)


def run() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true", help="also prove the gate rejects a temporary bad module")
    args = parser.parse_args()
    os.chdir(ROOT)
    project_modules = modules()
    # Explicit module targets ensure unindexed project sources are built and audited.
    build_modules(project_modules)
    lean_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], text=True).strip()
    with tempfile.TemporaryDirectory(prefix="math-axiom-gate-", dir=os.environ.get("TMPDIR")) as tmp:
        temp = Path(tmp)
        env = os.environ.copy()
        env["LEAN_PATH"] = str(temp) + os.pathsep + lean_path
        if args.self_test:
            external = temp / "ExternalProbe.lean"
            external.write_text("namespace ExternalProbe\naxiom hiddenAxiom : True\nend ExternalProbe\n", encoding="utf-8")
            subprocess.run(["lean", "--root", str(temp), "-o", str(external.with_suffix(".olean")), str(external)], env=env, check=True)
            probe = temp / "AxiomGateProbe.lean"
            probe.write_text("""import Std
import ExternalProbe
namespace AxiomGateProbe
axiom invented : True
axiom reduceWitness : Lean.reduceBool true = true
theorem inherited : True := ExternalProbe.hiddenAxiom
theorem admitted : True := by sorry
theorem nativeProof : (1 : Nat) + 1 = 2 := by native_decide
set_option linter.deprecated false in
theorem reduced : true = true := Lean.ofReduceBool true true reduceWitness
end AxiomGateProbe
""", encoding="utf-8")
            subprocess.run(["lean", "--root", str(temp), "-o", str(probe.with_suffix(".olean")), str(probe)], env=env, check=True)
            negative = temp / "negative.lean"
            negative.write_text(negative_probe_source(), encoding="utf-8")
            result = subprocess.run(["lean", str(negative)], env=env, text=True, capture_output=True)
            output = result.stdout + result.stderr
            expected = ("AxiomGateProbe.invented", "ExternalProbe.hiddenAxiom", "sorryAx",
                        "AxiomGateProbe.nativeProof._native", "Lean.ofReduceBool")
            if result.returncode == 0 or any(item not in output for item in expected):
                raise RuntimeError(f"axiom gate negative probe failed:\n{output}")
            print("axiom gate rejected local and imported custom axioms, sorryAx, native_decide, and Lean.ofReduceBool", flush=True)
        gate = temp / "gate.lean"
        gate.write_text(gate_source(project_modules), encoding="utf-8")
        subprocess.run(["lean", str(gate)], env=env, check=True)


if __name__ == "__main__":
    try:
        run()
    except (RuntimeError, subprocess.CalledProcessError) as exc:
        print(f"axiom gate failed: {exc}", file=sys.stderr)
        raise SystemExit(1)
