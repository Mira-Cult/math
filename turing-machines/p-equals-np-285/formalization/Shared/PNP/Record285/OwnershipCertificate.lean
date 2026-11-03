import Shared.PNP.Record285.OwnershipData
import Shared.PNP.Record285.OwnershipCheck

set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.GrammarCoreZero

theorem invariant_checked : invariantCheck logicalRows logicalMasks = true := by decide

theorem mapping_checked : mappingCheck logicalRows inputRows logicalMasks classMap graphMap = true := by decide

end Shared.PNP.Record285.OwnershipCore
