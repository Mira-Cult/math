import Shared.Beeping.NPcoNP.Grammar284SourceTails
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Kernel-checked source-tail equations for node indices 80–89.
These local equations require a separate full-file composition theorem. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard08
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row080 :
    tail81 = node producerGrammar.nodes[80]! ++ ",\n".toList ++ tail82 := by rfl
theorem row081 :
    tail82 = node producerGrammar.nodes[81]! ++ ",\n".toList ++ tail83 := by rfl
theorem row082 :
    tail83 = node producerGrammar.nodes[82]! ++ ",\n".toList ++ tail84 := by rfl
theorem row083 :
    tail84 = node producerGrammar.nodes[83]! ++ ",\n".toList ++ tail85 := by rfl
theorem row084 :
    tail85 = node producerGrammar.nodes[84]! ++ ",\n".toList ++ tail86 := by rfl
theorem row085 :
    tail86 = node producerGrammar.nodes[85]! ++ ",\n".toList ++ tail87 := by rfl
theorem row086 :
    tail87 = node producerGrammar.nodes[86]! ++ ",\n".toList ++ tail88 := by rfl
theorem row087 :
    tail88 = node producerGrammar.nodes[87]! ++ ",\n".toList ++ tail89 := by rfl
theorem row088 :
    tail89 = node producerGrammar.nodes[88]! ++ ",\n".toList ++ tail90 := by rfl
theorem row089 :
    tail90 = node producerGrammar.nodes[89]! ++ ",\n".toList ++ tail91 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard08
