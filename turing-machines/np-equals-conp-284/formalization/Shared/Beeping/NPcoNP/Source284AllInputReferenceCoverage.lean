import Shared.Beeping.NPcoNP.Source284AllInputCandidate
import Shared.Beeping.NPcoNP.Source284MarkedReferenceCoverage
import Shared.Beeping.NPcoNP.Source284GraphCanonical
import Shared.Beeping.NPcoNP.Source284EntryCanonicalConditional

/-! Full source-candidate coverage and a canonical complexity endpoint for
the checked *register graph*. The graph is not the literal binary tape table;
physical event-preserving refinement remains separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284AllInputReferenceCoverage

open ComplexityTheory
open Shared.Beeping
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284CanonicalConditional
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Parent290Coalesced

/-- For any canonical NP proof of the actual reference complement, one
fixed, arbitrarily large source candidate agrees on every natural input,
including zero-prefix inputs and arbitrary suffix aliases. -/
theorem reference_coverage_unbounded (h : referenceLanguageᶜ ∈ NP) (threshold : Nat) :
    ∃ j : Nat, threshold < j ∧ ∀ i : Nat, candidate j i = !reference i := by
  obtain ⟨j,hj,hcandidate⟩ := Source284AllInputCandidate.canonical_np_all_input_candidate
    Source284MarkedReferenceCoverage.prefixComplement
    (Source284MarkedReferenceCoverage.prefixComplement_mem_NP h) threshold
  refine ⟨j,hj,?_⟩
  intro i
  obtain ⟨x,suffix,hframe⟩ := Source284Parser.encodeFrame_surjective i
  have hc := hcandidate x suffix
  have hL := Source284MarkedReferenceCoverage.prefixComplement_frame x suffix
  rw [hframe] at hc hL
  rw [hL] at hc
  cases hbit : candidate j i <;> cases hreference : reference i <;> simp_all

theorem reference_coverage (h : referenceLanguageᶜ ∈ NP) :
    ∃ j, candidateLanguage j = referenceLanguageᶜ := by
  obtain ⟨j,_,hj⟩ := reference_coverage_unbounded h 0
  exact ⟨j,(candidate_agrees_iff j).1 hj⟩

/-- The checked 284 producer register graph is eventually silent exactly
when the pinned canonical NP and coNP classes coincide. This result does
not yet refine the graph to its serialized physical transition table. -/
theorem graph_eventuallySilent_iff_classes : target.system.erase.EventuallySilent ↔ NP = coNP :=
  Source284GraphCanonical.eventuallySilent_iff_classes reference_coverage

/-- The shared failure-event controller has the same unconditional
canonical class characterization. -/
theorem controller_eventuallySilent_iff_classes :
    (Shared.Beeping.Controller.system compare 0).EventuallySilent ↔ NP = coNP :=
  Source284CanonicalConditional.controller_iff_classes
    Source284ReferenceNP.reference_mem_NP Source284SelectorClosed.sat_hard
    Source284CandidateNP.candidate_mem_NP reference_coverage

/-- Entry-event convention for the same rejection search. -/
theorem entry_controller_eventuallySilent_iff_classes :
    (Shared.Beeping.CandidateEntryController.system compare 0).EventuallySilent ↔ NP = coNP :=
  Source284CanonicalConditional.entry_controller_iff_classes
    Source284ReferenceNP.reference_mem_NP Source284SelectorClosed.sat_hard
    Source284CandidateNP.candidate_mem_NP reference_coverage

/-- The corresponding uncoalesced producer register graph inherits the
same endpoint from the proved event refinement. -/
theorem producer_eventuallySilent_iff_classes :
    Parent290MaskData.program.system.erase.EventuallySilent ↔ NP = coNP :=
  Parent290Coalesced.eventual_silence_iff.trans graph_eventuallySilent_iff_classes

end Shared.Beeping.NPcoNP.Source284AllInputReferenceCoverage
