import Shared.PNP.Record285.OwnershipExpandedSimulation

/-! The extracted pre-contraction primitive graph has the literal machine's
event behavior. Packet extraction and earlier compiler passes remain open. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.OwnershipCore
open Shared.Beeping

noncomputable def acceptedExpansion : EventRefinement (system logicalRows) (system expandedRows) :=
  expansionRefinement logicalRows expandedRows expansionMap expansion_checked (by decide)

theorem expanded_eventuallySilent_iff_blank_start :
    (system expandedRows).EventuallySilent ↔ Record285.machine.system.EventuallySilent :=
  acceptedExpansion.eventuallySilent_iff.symm.trans eventuallySilent_iff_blank_start

theorem expanded_infinitelyMany_iff_blank_start :
    (system expandedRows).InfinitelyManyBeeps ↔ Record285.machine.system.InfinitelyManyBeeps :=
  acceptedExpansion.infinitelyManyBeeps_iff.symm.trans infinitelyMany_iff_blank_start

end Shared.PNP.Record285.OwnershipCore
