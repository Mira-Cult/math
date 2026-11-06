import Shared.Beeping.NPcoNP.Grammar284SourceTails
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Kernel-checked source-tail equations for node indices 20–29.
These local equations require a separate full-file composition theorem. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard02
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row020 :
    tail21 = node producerGrammar.nodes[20]! ++ ",\n".toList ++ tail22 := by rfl
theorem row021 :
    tail22 = node producerGrammar.nodes[21]! ++ ",\n".toList ++ tail23 := by rfl
theorem row022 :
    tail23 = node producerGrammar.nodes[22]! ++ ",\n".toList ++ tail24 := by rfl
theorem row023 :
    tail24 = node producerGrammar.nodes[23]! ++ ",\n".toList ++ tail25 := by rfl
theorem row024 :
    tail25 = node producerGrammar.nodes[24]! ++ ",\n".toList ++ tail26 := by rfl
theorem row025 :
    tail26 = node producerGrammar.nodes[25]! ++ ",\n".toList ++ tail27 := by rfl
theorem row026 :
    tail27 = node producerGrammar.nodes[26]! ++ ",\n".toList ++ tail28 := by rfl
theorem row027 :
    tail28 = node producerGrammar.nodes[27]! ++ ",\n".toList ++ tail29 := by rfl
theorem row028 :
    tail29 = node producerGrammar.nodes[28]! ++ ",\n".toList ++ tail30 := by rfl
theorem row029 :
    tail30 = node producerGrammar.nodes[29]! ++ ",\n".toList ++ tail31 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard02
