import Shared.Beeping.NPcoNP.Grammar284SourceTails
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Kernel-checked source-tail equations for node indices 150–159.
These local equations require a separate full-file composition theorem. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard15
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row150 :
    tail151 = node producerGrammar.nodes[150]! ++ ",\n".toList ++ tail152 := by rfl
theorem row151 :
    tail152 = node producerGrammar.nodes[151]! ++ ",\n".toList ++ tail153 := by rfl
theorem row152 :
    tail153 = node producerGrammar.nodes[152]! ++ ",\n".toList ++ tail154 := by rfl
theorem row153 :
    tail154 = node producerGrammar.nodes[153]! ++ ",\n".toList ++ tail155 := by rfl
theorem row154 :
    tail155 = node producerGrammar.nodes[154]! ++ ",\n".toList ++ tail156 := by rfl
theorem row155 :
    tail156 = node producerGrammar.nodes[155]! ++ ",\n".toList ++ tail157 := by rfl
theorem row156 :
    tail157 = node producerGrammar.nodes[156]! ++ ",\n".toList ++ tail158 := by rfl
theorem row157 :
    tail158 = node producerGrammar.nodes[157]! ++ ",\n".toList ++ tail159 := by rfl
theorem row158 :
    tail159 = node producerGrammar.nodes[158]! ++ ",\n".toList ++ tail160 := by rfl
theorem row159 :
    tail160 = node producerGrammar.nodes[159]! ++ "\n".toList ++ tail161 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard15
