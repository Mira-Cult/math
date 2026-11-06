import Shared.Beeping.NPcoNP.Source284EntryController
import Shared.Beeping.NPcoNP.Source284CanonicalConditional

/-! Class characterization of the candidate-entry atomic controller used by
the selected source convention. The four source-model obligations are still
explicit, and the result is not a refinement of the literal 284-state tape
machine. -/

namespace Shared.Beeping.NPcoNP.Source284CanonicalConditional

open ComplexityTheory
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CanonicalClasses
open Shared.Beeping.NPcoNP.Source284Comparison

/-- The candidate-entry controller has the same conditional class endpoint
as the rejection-beep controller. Entry and failure events need not occur at
the same time; the positive-segment simulation preserves eventual silence. -/
theorem entry_controller_iff_classes
    (member : referenceLanguage ∈ NP)
    (satHard : PolyRed CNF.sat referenceLanguage)
    (candidateMember : ∀ j, candidateLanguage j ∈ NP)
    (coverage : referenceLanguageᶜ ∈ NP →
      ∃ j, candidateLanguage j = referenceLanguageᶜ) :
    (Shared.Beeping.CandidateEntryController.system compare 0).EventuallySilent ↔ NP = coNP :=
  entrySimulation.toEventRefinement.eventuallySilent_iff.symm.trans
    (controller_iff_classes member satHard candidateMember coverage)

end Shared.Beeping.NPcoNP.Source284CanonicalConditional
