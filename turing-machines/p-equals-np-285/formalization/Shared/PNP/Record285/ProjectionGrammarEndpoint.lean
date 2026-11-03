import Shared.PNP.Record285.ProducerGrammarSemantics
import Shared.PNP.Record285.ProjectionGrammarCertificate
import Shared.PNP.Record285.ProjectionEndpoint
import Shared.PNP.Record285.ProjectionGrammarTextCertificate

/-! The exact serialized 21-register producer grammar and the literal
285-state machine have the same finite/infinite event behavior. The grammar
interpreter is total; this theorem does not identify earlier source passes. -/
namespace Shared.PNP.Record285.ProducerGrammar
open Shared.Beeping
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.OwnershipCore

noncomputable def acceptedRefinement : EventRefinement (OwnershipCore.system originalRows) (system grammar) :=
  (simulation grammar originalRows originalPositions source_graph_checked).toEventRefinement

theorem eventuallySilent_iff_blank_start :
    (system grammar).EventuallySilent ↔ Record285.machine.system.EventuallySilent :=
  acceptedRefinement.eventuallySilent_iff.symm.trans RegisterProjection.eventuallySilent_iff_blank_start

theorem infinitelyMany_iff_blank_start :
    (system grammar).InfinitelyManyBeeps ↔ Record285.machine.system.InfinitelyManyBeeps :=
  acceptedRefinement.infinitelyManyBeeps_iff.symm.trans RegisterProjection.infinitelyMany_iff_blank_start

end Shared.PNP.Record285.ProducerGrammar
