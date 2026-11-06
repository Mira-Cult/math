import Shared.Beeping.NPcoNP.Grammar284SourceTails
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Kernel-checked source-tail equations for node indices 90–99.
These local equations require a separate full-file composition theorem. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard09
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row090 :
    tail91 = node producerGrammar.nodes[90]! ++ ",\n".toList ++ tail92 := by rfl
theorem row091 :
    tail92 = node producerGrammar.nodes[91]! ++ ",\n".toList ++ tail93 := by rfl
theorem row092 :
    tail93 = node producerGrammar.nodes[92]! ++ ",\n".toList ++ tail94 := by rfl
theorem row093 :
    tail94 = node producerGrammar.nodes[93]! ++ ",\n".toList ++ tail95 := by rfl
theorem row094 :
    tail95 = node producerGrammar.nodes[94]! ++ ",\n".toList ++ tail96 := by rfl
theorem row095 :
    tail96 = node producerGrammar.nodes[95]! ++ ",\n".toList ++ tail97 := by rfl
theorem row096 :
    tail97 = node producerGrammar.nodes[96]! ++ ",\n".toList ++ tail98 := by rfl
theorem row097 :
    tail98 = node producerGrammar.nodes[97]! ++ ",\n".toList ++ tail99 := by rfl
theorem row098 :
    tail99 = node producerGrammar.nodes[98]! ++ ",\n".toList ++ tail100 := by rfl
theorem row099 :
    tail100 = node producerGrammar.nodes[99]! ++ ",\n".toList ++ tail101 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard09
