import Shared.Beeping.NPcoNP.Grammar284SourceTails
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Kernel-checked source-tail equations for node indices 40–49.
These local equations require a separate full-file composition theorem. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard04
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row040 :
    tail41 = node producerGrammar.nodes[40]! ++ ",\n".toList ++ tail42 := by rfl
theorem row041 :
    tail42 = node producerGrammar.nodes[41]! ++ ",\n".toList ++ tail43 := by rfl
theorem row042 :
    tail43 = node producerGrammar.nodes[42]! ++ ",\n".toList ++ tail44 := by rfl
theorem row043 :
    tail44 = node producerGrammar.nodes[43]! ++ ",\n".toList ++ tail45 := by rfl
theorem row044 :
    tail45 = node producerGrammar.nodes[44]! ++ ",\n".toList ++ tail46 := by rfl
theorem row045 :
    tail46 = node producerGrammar.nodes[45]! ++ ",\n".toList ++ tail47 := by rfl
theorem row046 :
    tail47 = node producerGrammar.nodes[46]! ++ ",\n".toList ++ tail48 := by rfl
theorem row047 :
    tail48 = node producerGrammar.nodes[47]! ++ ",\n".toList ++ tail49 := by rfl
theorem row048 :
    tail49 = node producerGrammar.nodes[48]! ++ ",\n".toList ++ tail50 := by rfl
theorem row049 :
    tail50 = node producerGrammar.nodes[49]! ++ ",\n".toList ++ tail51 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard04
