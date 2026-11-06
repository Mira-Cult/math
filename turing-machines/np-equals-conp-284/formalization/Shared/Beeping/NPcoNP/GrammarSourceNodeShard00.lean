import Shared.Beeping.NPcoNP.Grammar284SourceTails
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Kernel-checked source-tail equations for node indices 0–9.
These local equations require a separate full-file composition theorem. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard00
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row000 :
    tail1 = node producerGrammar.nodes[0]! ++ ",\n".toList ++ tail2 := by rfl
theorem row001 :
    tail2 = node producerGrammar.nodes[1]! ++ ",\n".toList ++ tail3 := by rfl
theorem row002 :
    tail3 = node producerGrammar.nodes[2]! ++ ",\n".toList ++ tail4 := by rfl
theorem row003 :
    tail4 = node producerGrammar.nodes[3]! ++ ",\n".toList ++ tail5 := by rfl
theorem row004 :
    tail5 = node producerGrammar.nodes[4]! ++ ",\n".toList ++ tail6 := by rfl
theorem row005 :
    tail6 = node producerGrammar.nodes[5]! ++ ",\n".toList ++ tail7 := by rfl
theorem row006 :
    tail7 = node producerGrammar.nodes[6]! ++ ",\n".toList ++ tail8 := by rfl
theorem row007 :
    tail8 = node producerGrammar.nodes[7]! ++ ",\n".toList ++ tail9 := by rfl
theorem row008 :
    tail9 = node producerGrammar.nodes[8]! ++ ",\n".toList ++ tail10 := by rfl
theorem row009 :
    tail10 = node producerGrammar.nodes[9]! ++ ",\n".toList ++ tail11 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard00
