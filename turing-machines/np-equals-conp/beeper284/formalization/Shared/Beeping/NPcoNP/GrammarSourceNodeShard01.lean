import Shared.Beeping.NPcoNP.Grammar284SourceTails
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Kernel-checked source-tail equations for node indices 10–19.
These local equations require a separate full-file composition theorem. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard01
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row010 :
    tail11 = node producerGrammar.nodes[10]! ++ ",\n".toList ++ tail12 := by rfl
theorem row011 :
    tail12 = node producerGrammar.nodes[11]! ++ ",\n".toList ++ tail13 := by rfl
theorem row012 :
    tail13 = node producerGrammar.nodes[12]! ++ ",\n".toList ++ tail14 := by rfl
theorem row013 :
    tail14 = node producerGrammar.nodes[13]! ++ ",\n".toList ++ tail15 := by rfl
theorem row014 :
    tail15 = node producerGrammar.nodes[14]! ++ ",\n".toList ++ tail16 := by rfl
theorem row015 :
    tail16 = node producerGrammar.nodes[15]! ++ ",\n".toList ++ tail17 := by rfl
theorem row016 :
    tail17 = node producerGrammar.nodes[16]! ++ ",\n".toList ++ tail18 := by rfl
theorem row017 :
    tail18 = node producerGrammar.nodes[17]! ++ ",\n".toList ++ tail19 := by rfl
theorem row018 :
    tail19 = node producerGrammar.nodes[18]! ++ ",\n".toList ++ tail20 := by rfl
theorem row019 :
    tail20 = node producerGrammar.nodes[19]! ++ ",\n".toList ++ tail21 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard01
