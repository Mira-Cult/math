import Shared.PNP.Record285.GrammarCoreZeroRewriteCertificate
import Shared.PNP.Record285.GrammarCoreZeroSimulation

/-! The pre-elimination graph has the literal machine's event behavior.
The byte-extraction and the earlier source-to-graph rewrites remain open. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarCoreZero
open Shared.Beeping
open Shared.PNP.Record285.GrammarCoreGraph

noncomputable def acceptedRewrite :
    EventRefinement (coreSystem producerRows) (coreSystem inputRows) :=
  rewriteRefinement inputRows producerRows masks zeroRows retainedMap
    input_invariant_checked selected_zero_checked rewrite_checked (by decide) (by decide)

theorem input_eventuallySilent_iff_blank_start :
    (coreSystem inputRows).EventuallySilent ↔ Record285.machine.system.EventuallySilent :=
  acceptedRewrite.eventuallySilent_iff.symm.trans producer_eventuallySilent_iff_blank_start

theorem input_infinitelyMany_iff_blank_start :
    (coreSystem inputRows).InfinitelyManyBeeps ↔ Record285.machine.system.InfinitelyManyBeeps :=
  acceptedRewrite.infinitelyManyBeeps_iff.symm.trans producer_infinitelyMany_iff_blank_start

end Shared.PNP.Record285.GrammarCoreZero
