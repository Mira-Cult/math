import Shared.Beeping.NPcoNP.Grammar284SourceTails
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Kernel-checked source-tail equations for node indices 130–139.
These local equations require a separate full-file composition theorem. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard13
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row130 :
    tail131 = node producerGrammar.nodes[130]! ++ ",\n".toList ++ tail132 := by rfl
theorem row131 :
    tail132 = node producerGrammar.nodes[131]! ++ ",\n".toList ++ tail133 := by rfl
theorem row132 :
    tail133 = node producerGrammar.nodes[132]! ++ ",\n".toList ++ tail134 := by rfl
theorem row133 :
    tail134 = node producerGrammar.nodes[133]! ++ ",\n".toList ++ tail135 := by rfl
theorem row134 :
    tail135 = node producerGrammar.nodes[134]! ++ ",\n".toList ++ tail136 := by rfl
theorem row135 :
    tail136 = node producerGrammar.nodes[135]! ++ ",\n".toList ++ tail137 := by rfl
theorem row136 :
    tail137 = node producerGrammar.nodes[136]! ++ ",\n".toList ++ tail138 := by rfl
theorem row137 :
    tail138 = node producerGrammar.nodes[137]! ++ ",\n".toList ++ tail139 := by rfl
theorem row138 :
    tail139 = node producerGrammar.nodes[138]! ++ ",\n".toList ++ tail140 := by rfl
theorem row139 :
    tail140 = node producerGrammar.nodes[139]! ++ ",\n".toList ++ tail141 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard13
