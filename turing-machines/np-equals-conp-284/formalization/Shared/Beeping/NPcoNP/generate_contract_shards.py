#!/usr/bin/env python3
"""Emit kernel-checkable 284 graph-contraction shards and coverage module.

The fixed bounds 279 and 185 are checked in Lean against candidate constants;
they do not assert any source, interpreter, or table binding.
"""
from pathlib import Path

OUT = Path("Shared/Beeping/NPcoNP")
NAMESPACE = "Shared.Beeping.NPcoNP"
WIDTH = 20

kinds = [
    ("Target", 279, "targetCheck producerFullRows producerNumbering.map"),
    ("Output", 185, "contractRowCheck producerFullRows producerNumbering graph.rows"),
]

for kind, limit, function in kinds:
    for start in range(0, limit, WIDTH):
        count = min(WIDTH, limit - start)
        name = f"Grammar284Contract{kind}Shard{start // WIDTH:02d}"
        source = f'''import {NAMESPACE}.GrammarContractCert
import {NAMESPACE}.Grammar284NumberingData
import {NAMESPACE}.GraphCandidate284Data

/-! Finite kernel check: {kind.lower()} indices {start}–{start+count-1}. -/
namespace {NAMESPACE}.{name}
open {NAMESPACE}.Grammar284
open {NAMESPACE}.GraphCandidate284
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem checked : contractCheckShard ({function}) {start} {count} = true := by decide
end {NAMESPACE}.{name}
'''
        (OUT / f"{name}.lean").write_text(source)

imports = [f"import {NAMESPACE}.Grammar284Numbering"]
for kind, limit, _ in kinds:
    imports.extend(f"import {NAMESPACE}.Grammar284Contract{kind}Shard{i:02d}"
                   for i in range((limit + WIDTH - 1) // WIDTH))

lines = imports + [
    "", "/-! The complete staged contraction check for the candidate arrays.",
    "This still does not bind the input rows to the producer grammar or bytes. -/",
    f"namespace {NAMESPACE}.Grammar284ContractCoverage",
    f"open {NAMESPACE}.Grammar284", f"open {NAMESPACE}.GraphCandidate284",
    "set_option maxRecDepth 16384", "set_option maxHeartbeats 12000000", "",
    "theorem fullRows_size : producerFullRows.size = 279 := by rfl", "",
]

for kind, limit, function in kinds:
    index_bound = "producerFullRows.size" if kind == "Target" else "producerNumbering.kept.size"
    theorem = "allTargets" if kind == "Target" else "allOutputs"
    size_theorem = "fullRows_size" if kind == "Target" else "producerNumbering_size"
    lines += [f"theorem {theorem} : ∀ i < {index_bound}, ({function}) i = true := by",
              "  intro i hi", f"  rw [{size_theorem}] at hi"]
    for start in range(0, limit, WIDTH):
        count = min(WIDTH, limit-start)
        shard = f"{NAMESPACE}.Grammar284Contract{kind}Shard{start // WIDTH:02d}.checked"
        lines += [f"  by_cases h{start} : i < {start+count}",
                  f"  · exact contractCheckShard_sound ({function}) {start} {count} i {shard} (by omega) (by omega)"]
    lines += ["  omega", ""]

lines += [
    "theorem producerEntry : target producerFullRows producerNumbering.map",
    "    (producerFullRows.size+1) 0 = some graph.entry := by rfl", "",
    "theorem producerOutputSize : producerNumbering.kept.size = graph.rows.size := by rfl", "",
    "theorem producerContract : contract producerFullRows = some graph := by",
    "  exact contract_of_checked producerFullRows producerNumbering graph",
    "    producerNumbering_correct producerNumbering_nonempty allTargets producerEntry",
    "    producerOutputSize allOutputs", "",
    "/-- A disconnected administrative self-loop still causes rejection. -/",
    'example : contract #[⟨"beep", [0]⟩, ⟨"jump", [1]⟩] = none := by decide', "",
    f"end {NAMESPACE}.Grammar284ContractCoverage", "",
]
(OUT / "Grammar284ContractCoverage.lean").write_text("\n".join(lines))
(OUT / "Grammar284ContractCoverageAudit.lean").write_text(
    f"import {NAMESPACE}.Grammar284ContractCoverage\n"
    f"#print axioms {NAMESPACE}.Grammar284ContractCoverage.producerContract\n")
