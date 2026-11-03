import Shared.PNP.Record285.OwnershipCoalescing

/-! The extracted 151-row ownership graph has the literal machine's event
behavior. Its source-packet extraction and earlier source compiler passes
remain separate obligations. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.OwnershipCore
open Shared.Beeping
open Shared.PNP.Record285.GrammarCoreGraph
open Shared.PNP.Record285.GrammarCoreZero

noncomputable def acceptedCoalescing : EventRefinement (system logicalRows) (coreSystem inputRows) :=
  coalescingRefinement logicalRows logicalMasks inputRows masks classMap graphMap
    invariant_checked input_invariant_checked mapping_checked (by decide) (by decide)

theorem eventuallySilent_iff_blank_start :
    (system logicalRows).EventuallySilent ↔ Record285.machine.system.EventuallySilent :=
  acceptedCoalescing.eventuallySilent_iff.trans input_eventuallySilent_iff_blank_start

theorem infinitelyMany_iff_blank_start :
    (system logicalRows).InfinitelyManyBeeps ↔ Record285.machine.system.InfinitelyManyBeeps :=
  acceptedCoalescing.infinitelyManyBeeps_iff.trans input_infinitelyMany_iff_blank_start

end Shared.PNP.Record285.OwnershipCore
