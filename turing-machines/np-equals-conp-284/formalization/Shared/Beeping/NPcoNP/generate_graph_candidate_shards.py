#!/usr/bin/env python3
"""Emit kernel-checkable candidate graph comparison shards and coverage.

The generated facts compare two finite Lean literals. They do not prove either
literal came from the producer source or physical table.
"""
from pathlib import Path

root = Path("Shared/Beeping/NPcoNP")
for shard in range(19):
    start, stop = 10 * shard, min(10 * shard + 10, 185)
    ns = f"GraphCandidate284Shard{shard:02d}"
    lines = ["import Shared.Beeping.NPcoNP.GraphCandidate284Data",
             "import Shared.Beeping.NPcoNP.GraphExtended284", "",
             "/-! Finite literal graph-to-program comparisons, not a producer binding. -/",
             f"namespace Shared.Beeping.NPcoNP.{ns}",
             "open Shared.Beeping.NPcoNP.GraphCandidate284",
             "open Shared.Beeping.NPcoNP.GraphExtended284",
             "open Shared.Beeping.NPcoNP.Parent290Coalesced",
             "set_option maxRecDepth 8192", "set_option maxHeartbeats 0", ""]
    for i in range(start, stop):
        lines.append(f"theorem row{i:03d} : rowMatches graph target ({i} : Fin 185) = true := by decide")
    lines += ["", f"end Shared.Beeping.NPcoNP.{ns}", ""]
    (root / f"{ns}.lean").write_text("\n".join(lines))

lines = [f"import Shared.Beeping.NPcoNP.GraphCandidate284Shard{i:02d}" for i in range(19)]
lines += ["", "/-! Coverage of the two literal data objects; the grammar and physical",
          "machine bindings remain open. -/",
          "namespace Shared.Beeping.NPcoNP.GraphCandidate284Coverage",
          "open Shared.Beeping.NPcoNP.GraphCandidate284",
          "open Shared.Beeping.NPcoNP.GraphExtended284",
          "open Shared.Beeping.NPcoNP.Parent290Coalesced", "",
          "set_option maxRecDepth 8192", "set_option maxHeartbeats 0", "",
          "theorem all_rows (i : Fin 185) : rowMatches graph target i = true := by",
          "  fin_cases i"]
lines += [f"  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard{i // 10:02d}.row{i:03d}" for i in range(185)]
lines += ["", "theorem graph_matches : graphMatches graph target = true := by",
          "  unfold graphMatches",
          "  simp only [Bool.and_eq_true, beq_iff_eq]",
          "  refine ⟨⟨rfl, rfl⟩, ?_⟩",
          "  apply List.all_eq_true.mpr",
          "  intro i _",
          "  exact all_rows i", "",
          "theorem agrees : graph.rows.size = 185 ∧ graph.entry = target.start.val ∧",
          "    ∀ i : Fin 185, ∃ row, graph.rows[i.val]? = some row ∧",
          "      decode row = some target.code[i] := target_sound graph graph_matches", "",
          "end Shared.Beeping.NPcoNP.GraphCandidate284Coverage", ""]
(root / "GraphCandidate284Coverage.lean").write_text("\n".join(lines))
