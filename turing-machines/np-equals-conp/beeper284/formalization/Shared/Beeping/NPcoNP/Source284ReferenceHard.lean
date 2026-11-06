import Shared.Beeping.NPcoNP.Source284SelectorClosed

/-! Uniform hardness and class consequences for the actual source reference.
This does not supply the missing source candidate coverage or a physical
machine simulation. -/
namespace Shared.Beeping.NPcoNP.Source284ReferenceHard

open ComplexityTheory
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CanonicalClasses
open Shared.Beeping.NPcoNP.Source284CanonicalConditional

/-- Every canonical NP language uniformly reduces to the source reference
on all raw bitstrings. Both reduction maps run in the pinned TM2 model. -/
theorem np_hard (L : DecisionProblem) (hL : L ∈ NP) : PolyRed L referenceLanguage := by
  obtain ⟨f,hf,hf_correct⟩ := GeneratorGateListClosed.satComplete.hard L hL
  obtain ⟨g,hg,hg_correct⟩ := Source284SelectorClosed.sat_hard
  refine ⟨fun x => g (f x), TM2Compose.isPolyTime_comp f g hf hg, ?_⟩
  intro x
  exact (hf_correct x).trans (hg_correct (f x))

/-- The complement of the source reference belongs to canonical NP exactly
when canonical NP equals canonical coNP. -/
theorem reference_complement_iff_classes : referenceLanguageᶜ ∈ NP ↔ NP = coNP :=
  Source284CanonicalConditional.reference_complement_iff_classes
    Source284ReferenceNP.reference_mem_NP Source284SelectorClosed.sat_hard

end Shared.Beeping.NPcoNP.Source284ReferenceHard
