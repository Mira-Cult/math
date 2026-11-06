import Shared.Beeping.NPcoNP.Source284ReferenceNP
import Shared.Beeping.NPcoNP.Source284EntryCanonicalConditional

/-! The source reference's canonical NP membership is now discharged. The
remaining source-specific hardness, fixed-candidate membership and coverage
premises are explicit. The theorem remains about the atomic candidate-entry
controller; it does not bind the literal 284-state table. -/

namespace Shared.Beeping.NPcoNP.Source284ReducedConditional

open ComplexityTheory
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CanonicalClasses
open Shared.Beeping.NPcoNP.Source284CanonicalConditional
open Shared.Beeping.NPcoNP.Source284Comparison

theorem entry_controller_iff_classes
    (satHard : PolyRed CNF.sat referenceLanguage)
    (candidateMember : ∀ j, candidateLanguage j ∈ NP)
    (coverage : referenceLanguageᶜ ∈ NP →
      ∃ j, candidateLanguage j = referenceLanguageᶜ) :
    (Shared.Beeping.CandidateEntryController.system compare 0).EventuallySilent ↔ NP = coNP :=
  Source284CanonicalConditional.entry_controller_iff_classes
    Source284ReferenceNP.reference_mem_NP satHard candidateMember coverage

end Shared.Beeping.NPcoNP.Source284ReducedConditional
