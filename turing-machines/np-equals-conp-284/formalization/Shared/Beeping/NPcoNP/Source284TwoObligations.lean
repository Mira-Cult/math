import Shared.Beeping.NPcoNP.Source284CandidateNP
import Shared.Beeping.NPcoNP.Source284ReducedConditional

/-! The 284 source controller after discharging both canonical NP membership
obligations. SAT hardness and single-program coverage remain explicit; no
literal tape-machine refinement is asserted. -/

namespace Shared.Beeping.NPcoNP.Source284TwoObligations

open ComplexityTheory
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CanonicalClasses
open Shared.Beeping.NPcoNP.Source284CanonicalConditional
open Shared.Beeping.NPcoNP.Source284Comparison

theorem entry_controller_iff_classes
    (satHard : PolyRed CNF.sat referenceLanguage)
    (coverage : referenceLanguageᶜ ∈ NP →
      ∃ j, candidateLanguage j = referenceLanguageᶜ) :
    (Shared.Beeping.CandidateEntryController.system compare 0).EventuallySilent ↔ NP = coNP :=
  Source284ReducedConditional.entry_controller_iff_classes
    satHard Source284CandidateNP.all_candidates_mem_NP coverage

end Shared.Beeping.NPcoNP.Source284TwoObligations
