import Shared.PNP.Record285.GrammarCoreZeroCheck
import Shared.PNP.Record285.GrammarCoreZeroData

set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarCoreZero

theorem input_invariant_checked : check inputRows masks = true := by decide

theorem selected_zero_checked : zeroRows.all (selectedZero inputRows masks) = true := by decide

end Shared.PNP.Record285.GrammarCoreZero
