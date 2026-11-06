import Shared.Beeping.NPcoNP.Grammar284SourceTails
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Kernel-checked source-tail equations for node indices 100–109.
These local equations require a separate full-file composition theorem. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard10
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row100 :
    tail101 = node producerGrammar.nodes[100]! ++ ",\n".toList ++ tail102 := by rfl
theorem row101 :
    tail102 = node producerGrammar.nodes[101]! ++ ",\n".toList ++ tail103 := by rfl
theorem row102 :
    tail103 = node producerGrammar.nodes[102]! ++ ",\n".toList ++ tail104 := by rfl
theorem row103 :
    tail104 = node producerGrammar.nodes[103]! ++ ",\n".toList ++ tail105 := by rfl
theorem row104 :
    tail105 = node producerGrammar.nodes[104]! ++ ",\n".toList ++ tail106 := by rfl
theorem row105 :
    tail106 = node producerGrammar.nodes[105]! ++ ",\n".toList ++ tail107 := by rfl
theorem row106 :
    tail107 = node producerGrammar.nodes[106]! ++ ",\n".toList ++ tail108 := by rfl
theorem row107 :
    tail108 = node producerGrammar.nodes[107]! ++ ",\n".toList ++ tail109 := by rfl
theorem row108 :
    tail109 = node producerGrammar.nodes[108]! ++ ",\n".toList ++ tail110 := by rfl
theorem row109 :
    tail110 = node producerGrammar.nodes[109]! ++ ",\n".toList ++ tail111 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard10
