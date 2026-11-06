import Shared.Beeping.NPcoNP.Grammar284SourceTails
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Kernel-checked source-tail equations for node indices 110–119.
These local equations require a separate full-file composition theorem. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard11
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row110 :
    tail111 = node producerGrammar.nodes[110]! ++ ",\n".toList ++ tail112 := by rfl
theorem row111 :
    tail112 = node producerGrammar.nodes[111]! ++ ",\n".toList ++ tail113 := by rfl
theorem row112 :
    tail113 = node producerGrammar.nodes[112]! ++ ",\n".toList ++ tail114 := by rfl
theorem row113 :
    tail114 = node producerGrammar.nodes[113]! ++ ",\n".toList ++ tail115 := by rfl
theorem row114 :
    tail115 = node producerGrammar.nodes[114]! ++ ",\n".toList ++ tail116 := by rfl
theorem row115 :
    tail116 = node producerGrammar.nodes[115]! ++ ",\n".toList ++ tail117 := by rfl
theorem row116 :
    tail117 = node producerGrammar.nodes[116]! ++ ",\n".toList ++ tail118 := by rfl
theorem row117 :
    tail118 = node producerGrammar.nodes[117]! ++ ",\n".toList ++ tail119 := by rfl
theorem row118 :
    tail119 = node producerGrammar.nodes[118]! ++ ",\n".toList ++ tail120 := by rfl
theorem row119 :
    tail120 = node producerGrammar.nodes[119]! ++ ",\n".toList ++ tail121 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard11
