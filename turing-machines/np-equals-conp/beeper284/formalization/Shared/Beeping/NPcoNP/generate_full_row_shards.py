"""Generate serial kernel-checkable full-row shards and their coverage proof.

The candidate row data and expansion are supplied by other modules. These
proofs check their correspondence; they do not establish the grammar-to-JSON
or producer-algorithm correspondence.
"""
import argparse
from pathlib import Path

HERE = Path(__file__).resolve().parent


def write_sources(out):
    out.mkdir(parents=True, exist_ok=True)
    prefix = "Shared.Beeping.NPcoNP"
    for shard in range(28):
        lo = 10 * shard
        length = min(10, 279 - lo)
        module = f"GrammarFullRowsShard{shard:02d}"
        src = f'''import {prefix}.ExpansionTrace.Final
import {prefix}.Grammar284FullRows
import {prefix}.GrammarFullGraphRowCheck

/-! Kernel check for full expansion row indices {lo} through {lo + length - 1}. -/
namespace {prefix}.{module}
open {prefix}.Grammar284
open {prefix}.Grammar284.ExpandSteps.ProducerTrace
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem checked : indexedRowShard traceState557.acc producerFullRows {lo} {length} = true := by decide

end {prefix}.{module}
'''
        (out / f"{module}.lean").write_text(src, encoding="utf-8")

    imports = "\n".join(f"import {prefix}.GrammarFullRowsShard{i:02d}" for i in range(28))
    lines = [imports, "", "/-! Coverage of every row in the checked Lean AST expansion.",
             "The JSON-byte and producer-algorithm bindings remain separate. -/",
             f"namespace {prefix}.GrammarFullRowsCoverage",
             f"open {prefix}.Grammar284",
             f"open {prefix}.Grammar284.ExpandSteps.ProducerTrace", "",
             "set_option maxRecDepth 16384", "set_option maxHeartbeats 12000000", "",
             "theorem allRows (i : Nat) (hi : i < traceState557.acc.leaves.size) :",
             "    indexedRowCheck traceState557.acc producerFullRows i = true := by",
             "  have hbound : i < 279 := by simpa [producerLeafCount] using hi"]
    for shard in range(28):
        lo = 10 * shard
        length = min(10, 279 - lo)
        if shard < 27:
            lines += [f"  by_cases h{shard} : i < {lo+length}",
                      f"  · exact indexedRowShard_sound _ _ {lo} {length} i {prefix}.GrammarFullRowsShard{shard:02d}.checked (by omega) (by omega)"]
        else:
            lines += [f"  exact indexedRowShard_sound _ _ {lo} {length} i {prefix}.GrammarFullRowsShard{shard:02d}.checked (by omega) (by omega)"]
    lines += ["", "theorem producerFullGraph : fullGraph producerGrammar 53 = some producerFullRows := by",
              "  apply fullGraph_of_checked_rows producerGrammar 53 traceState557.acc producerFullRows producerExpand",
              "  · rw [producerLeafCount]; rfl", "  · exact allRows", "",
              f"end {prefix}.GrammarFullRowsCoverage", ""]
    (out / "GrammarFullRowsCoverage.lean").write_text("\n".join(lines), encoding="utf-8")
    (out / "GrammarFullRowsCoverageAudit.lean").write_text(
        f"import {prefix}.GrammarFullRowsCoverage\n\n"
        f"#print axioms {prefix}.GrammarFullRowsCoverage.allRows\n"
        f"#print axioms {prefix}.GrammarFullRowsCoverage.producerFullGraph\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=HERE)
    write_sources(parser.parse_args().output_dir)


if __name__ == "__main__":
    main()
