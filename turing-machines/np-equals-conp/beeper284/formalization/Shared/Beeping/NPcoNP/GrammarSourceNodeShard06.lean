import Shared.Beeping.NPcoNP.Grammar284SourceTails
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Kernel-checked source-tail equations for node indices 60–69.
These local equations require a separate full-file composition theorem. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard06
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row060 :
    tail61 = node producerGrammar.nodes[60]! ++ ",\n".toList ++ tail62 := by rfl
theorem row061 :
    tail62 = node producerGrammar.nodes[61]! ++ ",\n".toList ++ tail63 := by rfl
theorem row062 :
    tail63 = node producerGrammar.nodes[62]! ++ ",\n".toList ++ tail64 := by rfl
theorem row063 :
    tail64 = node producerGrammar.nodes[63]! ++ ",\n".toList ++ tail65 := by rfl
theorem row064 :
    tail65 = node producerGrammar.nodes[64]! ++ ",\n".toList ++ tail66 := by rfl
theorem row065 :
    tail66 = node producerGrammar.nodes[65]! ++ ",\n".toList ++ tail67 := by rfl
theorem row066 :
    tail67 = node producerGrammar.nodes[66]! ++ ",\n".toList ++ tail68 := by rfl
theorem row067 :
    tail68 = node producerGrammar.nodes[67]! ++ ",\n".toList ++ tail69 := by rfl
theorem row068 :
    tail69 = node producerGrammar.nodes[68]! ++ ",\n".toList ++ tail70 := by rfl
theorem row069 :
    tail70 = node producerGrammar.nodes[69]! ++ ",\n".toList ++ tail71 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.SourceNodeShard06
