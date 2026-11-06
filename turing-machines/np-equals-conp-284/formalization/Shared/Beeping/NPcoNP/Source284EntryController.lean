import Shared.Beeping.CandidateEntryController
import Shared.Beeping.NPcoNP.Source284ComparisonBridge

/-! The pinned 284 source uses the candidate-entry beep convention. This
instantiates an abstract atomic-comparison simulation only: there is no claim
here that the source program or 284-state table has been refined to it. -/
namespace Shared.Beeping.NPcoNP.Source284Comparison

def entrySimulation : SegmentSimulation (Controller.system compare 0)
    (CandidateEntryController.system compare 0) :=
  CandidateEntryController.simulation compare 0

theorem entry_controller_silent_iff :
    (CandidateEntryController.system compare 0).EventuallySilent ↔
      ∃ j, ∀ i, candidate j i = !reference i := by
  rw [← entrySimulation.toEventRefinement.eventuallySilent_iff]
  exact controller_silent_iff

theorem entry_controller_infinite_iff :
    (Controller.system compare 0).InfinitelyManyBeeps ↔
      (CandidateEntryController.system compare 0).InfinitelyManyBeeps :=
  entrySimulation.toEventRefinement.infinitelyManyBeeps_iff

end Shared.Beeping.NPcoNP.Source284Comparison
