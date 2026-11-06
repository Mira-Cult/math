import Shared.Beeping.NPcoNP.Grammar284SourceTails
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Kernel-checked source-tail equations for node indices 30–39.
These local equations require a separate full-file composition theorem. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard03
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row030 :
    tail31 = node producerGrammar.nodes[30]! ++ ",\n".toList ++ tail32 := by rfl
theorem row031 :
    tail32 = node producerGrammar.nodes[31]! ++ ",\n".toList ++ tail33 := by rfl
theorem row032 :
    tail33 = node producerGrammar.nodes[32]! ++ ",\n".toList ++ tail34 := by rfl
theorem row033 :
    tail34 = node producerGrammar.nodes[33]! ++ ",\n".toList ++ tail35 := by rfl
theorem row034 :
    tail35 = node producerGrammar.nodes[34]! ++ ",\n".toList ++ tail36 := by rfl
theorem row035 :
    tail36 = node producerGrammar.nodes[35]! ++ ",\n".toList ++ tail37 := by rfl
theorem row036 :
    tail37 = node producerGrammar.nodes[36]! ++ ",\n".toList ++ tail38 := by rfl
theorem row037 :
    tail38 = node producerGrammar.nodes[37]! ++ ",\n".toList ++ tail39 := by rfl
theorem row038 :
    tail39 = node producerGrammar.nodes[38]! ++ ",\n".toList ++ tail40 := by rfl
theorem row039 :
    tail40 = node producerGrammar.nodes[39]! ++ ",\n".toList ++ tail41 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard03
