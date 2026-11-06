import Shared.Beeping.NPcoNP.Grammar284SourceTails
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Kernel-checked source-tail equations for node indices 50–59.
These local equations require a separate full-file composition theorem. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard05
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row050 :
    tail51 = node producerGrammar.nodes[50]! ++ ",\n".toList ++ tail52 := by rfl
theorem row051 :
    tail52 = node producerGrammar.nodes[51]! ++ ",\n".toList ++ tail53 := by rfl
theorem row052 :
    tail53 = node producerGrammar.nodes[52]! ++ ",\n".toList ++ tail54 := by rfl
theorem row053 :
    tail54 = node producerGrammar.nodes[53]! ++ ",\n".toList ++ tail55 := by rfl
theorem row054 :
    tail55 = node producerGrammar.nodes[54]! ++ ",\n".toList ++ tail56 := by rfl
theorem row055 :
    tail56 = node producerGrammar.nodes[55]! ++ ",\n".toList ++ tail57 := by rfl
theorem row056 :
    tail57 = node producerGrammar.nodes[56]! ++ ",\n".toList ++ tail58 := by rfl
theorem row057 :
    tail58 = node producerGrammar.nodes[57]! ++ ",\n".toList ++ tail59 := by rfl
theorem row058 :
    tail59 = node producerGrammar.nodes[58]! ++ ",\n".toList ++ tail60 := by rfl
theorem row059 :
    tail60 = node producerGrammar.nodes[59]! ++ ",\n".toList ++ tail61 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard05
