import Shared.PNP.Record285.ProjectionGrammarData

/-! The untrusted graph extraction is checked against the producer grammar.
Each of the 177 rows is checked for its operation and both branch outcomes. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ProducerGrammar
open Shared.PNP.Record285.RegisterProjection

theorem source_graph_checked : check grammar originalRows originalPositions = true := by decide

end Shared.PNP.Record285.ProducerGrammar
