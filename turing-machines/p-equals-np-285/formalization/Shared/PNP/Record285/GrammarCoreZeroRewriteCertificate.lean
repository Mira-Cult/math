import Shared.PNP.Record285.GrammarCoreZeroRewrite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarCoreZero
open Shared.PNP.Record285.GrammarCoreGraph

theorem rewrite_checked : rewriteCheck inputRows producerRows zeroRows retainedMap = true := by decide

end Shared.PNP.Record285.GrammarCoreZero
