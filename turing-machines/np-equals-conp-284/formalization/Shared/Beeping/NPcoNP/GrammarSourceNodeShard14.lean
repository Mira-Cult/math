import Shared.Beeping.NPcoNP.Grammar284SourceTails
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Kernel-checked source-tail equations for node indices 140–149.
These local equations require a separate full-file composition theorem. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard14
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row140 :
    tail141 = node producerGrammar.nodes[140]! ++ ",\n".toList ++ tail142 := by rfl
theorem row141 :
    tail142 = node producerGrammar.nodes[141]! ++ ",\n".toList ++ tail143 := by rfl
theorem row142 :
    tail143 = node producerGrammar.nodes[142]! ++ ",\n".toList ++ tail144 := by rfl
theorem row143 :
    tail144 = node producerGrammar.nodes[143]! ++ ",\n".toList ++ tail145 := by rfl
theorem row144 :
    tail145 = node producerGrammar.nodes[144]! ++ ",\n".toList ++ tail146 := by rfl
theorem row145 :
    tail146 = node producerGrammar.nodes[145]! ++ ",\n".toList ++ tail147 := by rfl
theorem row146 :
    tail147 = node producerGrammar.nodes[146]! ++ ",\n".toList ++ tail148 := by rfl
theorem row147 :
    tail148 = node producerGrammar.nodes[147]! ++ ",\n".toList ++ tail149 := by rfl
theorem row148 :
    tail149 = node producerGrammar.nodes[148]! ++ ",\n".toList ++ tail150 := by rfl
theorem row149 :
    tail150 = node producerGrammar.nodes[149]! ++ ",\n".toList ++ tail151 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard14
