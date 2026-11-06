import Shared.Beeping.NPcoNP.Grammar284SourceTails
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Kernel-checked source-tail equations for node indices 120–129.
These local equations require a separate full-file composition theorem. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard12
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row120 :
    tail121 = node producerGrammar.nodes[120]! ++ ",\n".toList ++ tail122 := by rfl
theorem row121 :
    tail122 = node producerGrammar.nodes[121]! ++ ",\n".toList ++ tail123 := by rfl
theorem row122 :
    tail123 = node producerGrammar.nodes[122]! ++ ",\n".toList ++ tail124 := by rfl
theorem row123 :
    tail124 = node producerGrammar.nodes[123]! ++ ",\n".toList ++ tail125 := by rfl
theorem row124 :
    tail125 = node producerGrammar.nodes[124]! ++ ",\n".toList ++ tail126 := by rfl
theorem row125 :
    tail126 = node producerGrammar.nodes[125]! ++ ",\n".toList ++ tail127 := by rfl
theorem row126 :
    tail127 = node producerGrammar.nodes[126]! ++ ",\n".toList ++ tail128 := by rfl
theorem row127 :
    tail128 = node producerGrammar.nodes[127]! ++ ",\n".toList ++ tail129 := by rfl
theorem row128 :
    tail129 = node producerGrammar.nodes[128]! ++ ",\n".toList ++ tail130 := by rfl
theorem row129 :
    tail130 = node producerGrammar.nodes[129]! ++ ",\n".toList ++ tail131 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard12
