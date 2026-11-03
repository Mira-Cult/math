import Shared.PNP.Record285.OwnershipExpandedData
import Shared.PNP.Record285.OwnershipExpandedCheck

set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.OwnershipCore

theorem expansion_checked : expansionCheck logicalRows expandedRows expansionMap = true := by decide

end Shared.PNP.Record285.OwnershipCore
