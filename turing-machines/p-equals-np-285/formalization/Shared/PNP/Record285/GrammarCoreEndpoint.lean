import Shared.PNP.Record285.GrammarCoreGraphCertificate
import Shared.PNP.Record285.GrammarCoreGraphTextCertificate
import Shared.PNP.Record285.GrammarCoreSemantics

/-! The checked 172-row core graph has the literal machine's event behavior.
This is not yet a checked correspondence with the producer source program or
the canonical complexity classes. -/
namespace Shared.PNP.Record285.GrammarCoreGraph
open Shared.Beeping

noncomputable def producerRefinement :
    EventRefinement (coreSystem producerRows) GrammarControlGraph.system :=
  coreRefinement producerRows producerPositions producer_graph_checked

noncomputable def producerPhysicalRefinement :
    EventRefinement (coreSystem producerRows) GrammarOperationalRun.physicalSystem :=
  producerRefinement.trans GrammarControlGraph.physicalRefinement

theorem producer_eventuallySilent_iff_blank_start :
    (coreSystem producerRows).EventuallySilent ↔ Record285.machine.system.EventuallySilent :=
  producerRefinement.eventuallySilent_iff.trans GrammarControlGraph.eventuallySilent_iff_blank_start

theorem producer_infinitelyMany_iff_blank_start :
    (coreSystem producerRows).InfinitelyManyBeeps ↔ Record285.machine.system.InfinitelyManyBeeps :=
  producerRefinement.infinitelyManyBeeps_iff.trans GrammarControlGraph.infinitelyMany_iff_blank_start

end Shared.PNP.Record285.GrammarCoreGraph
