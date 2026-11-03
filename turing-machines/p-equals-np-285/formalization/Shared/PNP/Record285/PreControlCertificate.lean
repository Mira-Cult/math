import Shared.PNP.Record285.PreControlPositions

/-! Verify all primitive occurrences of the pre-control grammar against the
same graph used by the checked 21-to-18 register projection. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.PreControlGrammar
open Shared.PNP.Record285.ProducerGrammar
open Shared.PNP.Record285.RegisterProjection

theorem graph_checked : check grammar originalRows positions = true := by decide

end Shared.PNP.Record285.PreControlGrammar
