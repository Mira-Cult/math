import Shared.PNP.Record285.ProducerGrammarSemantics
import Shared.PNP.Record285.PreControlCertificate
import Shared.PNP.Record285.ProjectionGrammarEndpoint
import Shared.PNP.Record285.PreControlGrammarTextCertificate

/-! The frozen pre-control producer grammar, the post-control grammar, and
the literal blank-start machine have the same event behavior. The common
graph checker accounts for silent administrative steps with positive progress;
it does not assume or trust the producer's control-rewrite certificate. -/
namespace Shared.PNP.Record285.PreControlGrammar
open Shared.Beeping
open Shared.PNP.Record285.ProducerGrammar
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.OwnershipCore

noncomputable def acceptedRefinement : EventRefinement (OwnershipCore.system originalRows) (system grammar) :=
  (simulation grammar originalRows positions graph_checked).toEventRefinement

/-- Every checked graph action consumes at most 32 grammar transitions. -/
theorem checked_boundary_bound (g : Data) (rows : Array OwnershipCore.Row)
    (pos : Array (List Bool)) (h : check g rows pos = true) (i : Nat) :
    (simulation g rows pos h).boundary (i+1) ≤ (simulation g rows pos h).boundary i + 32 := by
  have hr := (simulation g rows pos h).related_boundary i
  change ProducerGrammar.Rel rows pos _ _ at hr
  have hk := (Classical.choose_spec (local_progress g rows pos h _ _ hr)).1
  change _ + duration g rows pos h _ _ ≤ _ + 32
  simp only [duration,dif_pos hr]
  omega

/-- At corresponding graph boundaries the two complete, unbounded banks agree. -/
theorem banks_agree_at_boundaries (i : Nat) :
    ((system grammar).run (acceptedRefinement.boundary i)).bank =
      ((system ProducerGrammar.grammar).run (ProducerGrammar.acceptedRefinement.boundary i)).bank := by
  have hpre := acceptedRefinement.related i
  have hpost := ProducerGrammar.acceptedRefinement.related i
  change ProducerGrammar.Rel originalRows positions _ _ at hpre
  change ProducerGrammar.Rel originalRows originalPositions _ _ at hpost
  exact hpre.2.1.symm.trans hpost.2.1

/-- Each positive pre-control segment has an event exactly when its paired
post-control segment does; both refinements also prove uniqueness per segment. -/
theorem event_segments_agree (i : Nat) :
    (∃ j, acceptedRefinement.boundary i ≤ j ∧ j < acceptedRefinement.boundary (i+1) ∧
      (system grammar).BeepAt j) ↔
    (∃ j, ProducerGrammar.acceptedRefinement.boundary i ≤ j ∧
      j < ProducerGrammar.acceptedRefinement.boundary (i+1) ∧
      (system ProducerGrammar.grammar).BeepAt j) :=
  (acceptedRefinement.event_iff i).symm.trans (ProducerGrammar.acceptedRefinement.event_iff i)

theorem eventuallySilent_iff_blank_start :
    (system grammar).EventuallySilent ↔ Record285.machine.system.EventuallySilent :=
  acceptedRefinement.eventuallySilent_iff.symm.trans RegisterProjection.eventuallySilent_iff_blank_start

theorem infinitelyMany_iff_blank_start :
    (system grammar).InfinitelyManyBeeps ↔ Record285.machine.system.InfinitelyManyBeeps :=
  acceptedRefinement.infinitelyManyBeeps_iff.symm.trans RegisterProjection.infinitelyMany_iff_blank_start

theorem eventuallySilent_iff_post_control :
    (system grammar).EventuallySilent ↔ (system ProducerGrammar.grammar).EventuallySilent :=
  eventuallySilent_iff_blank_start.trans ProducerGrammar.eventuallySilent_iff_blank_start.symm

theorem infinitelyMany_iff_post_control :
    (system grammar).InfinitelyManyBeeps ↔ (system ProducerGrammar.grammar).InfinitelyManyBeeps :=
  infinitelyMany_iff_blank_start.trans ProducerGrammar.infinitelyMany_iff_blank_start.symm

end Shared.PNP.Record285.PreControlGrammar
