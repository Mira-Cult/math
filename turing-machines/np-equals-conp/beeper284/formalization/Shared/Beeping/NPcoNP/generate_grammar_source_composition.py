"""Generate the ordered composition of the 160 checked source-node rows.

The generated theorem checks the fixed-layout character representation of
the Lean grammar. It does not claim a general JSON-parser correctness result.
"""

import argparse
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    lines = [
        f"import Shared.Beeping.NPcoNP.GrammarSourceNodeShard{i:02d}"
        for i in range(16)
    ]
    lines.extend([
        "import Shared.Beeping.NPcoNP.Grammar284SourceChain", "",
        "/-! Composition of all 160 source-node certificates. This establishes the",
        "fixed-layout character representation, not the correctness of a general JSON",
        "parser or the filesystem SHA-256. -/",
        "namespace Shared.Beeping.NPcoNP.Grammar284.SourceComposition",
        "open Shared.Beeping.NPcoNP.Grammar284.SourceTails",
        "open Shared.Beeping.NPcoNP.Grammar284.SourceRender", "",
        "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "",
    ])
    # Compose ten local equations at a time, working from the final node
    # backward. Each named theorem keeps the elaboration target bounded.
    for shard in reversed(range(16)):
        start = 10 * shard
        lines.append(
            f"theorem chain{start:03d} : RenderChain "
            f"(producerGrammar.nodes.toList.drop {start}) tail{start + 1} tail161 := by"
        )
        for i in range(start, min(start + 10, 159)):
            lines.extend([
                "  apply RenderChain.cons",
                f"  · exact SourceNodeShard{i // 10:02d}.row{i:03d}",
            ])
        if shard == 15:
            lines.extend(["  apply RenderChain.last", "  exact SourceNodeShard15.row159"])
        else:
            lines.append(f"  exact chain{start + 10:03d}")
        lines.append("")
    lines.extend([
        "theorem producerChain : RenderChain producerGrammar.nodes.toList tail1 tail161 := by",
        "  exact chain000", "",
        "theorem footer_eq : footer producerGrammar = tail161 := by rfl", "",
        "theorem source_to_render : SourceChars.source.toList = render producerGrammar := by",
        "  rw [source_toList]", "  unfold render",
        "  rw [footer_eq, nodes_eq_of_chain producerChain]", "  rfl", "",
        "theorem source_eq_serialization :",
        "    SourceChars.source = String.ofList (render producerGrammar) := by",
        "  simpa only [String.ofList_toList] using congrArg String.ofList source_to_render", "",
        "/-- Every embedded source byte is covered by the UTF-8 encoding of the",
        "fixed-layout rendering. This does not assert a filesystem hash or parser",
        "correctness theorem. -/",
        "theorem source_bytes_to_render :",
        "    SourceChars.source.toByteArray = (render producerGrammar).utf8Encode := by",
        "  rw [← String.utf8Encode_toList, source_to_render]", "",
        "end Shared.Beeping.NPcoNP.Grammar284.SourceComposition", "",
    ])
    args.output.write_text("\n".join(lines), encoding="utf-8")


if __name__ == "__main__":
    main()
