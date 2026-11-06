import Shared.Beeping.NPcoNP.Grammar284Data

namespace Shared.Beeping.NPcoNP.Grammar284

set_option maxRecDepth 4096

theorem producerGrammar_node_count : producerGrammar.nodes.size = 160 := by decide
theorem producerGrammar_register_count : producerGrammar.registers.size = 12 := by decide
theorem producerGrammar_root : producerGrammar.root = 159 := by decide

end Shared.Beeping.NPcoNP.Grammar284
