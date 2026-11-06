import Shared.Beeping.NPcoNP.Source284GraphSilence
import Shared.Beeping.NPcoNP.Source284ReferenceComplete
import Shared.Beeping.NPcoNP.Source284CandidateNP
import Shared.Beeping.NPcoNP.Source284GuardCompilerInterface

/-! Canonical class consequences of the checked 284 producer register graph.
The graph uses unbounded natural registers; no literal physical-table
refinement or unproved candidate-coverage theorem is assumed here. -/
namespace Shared.Beeping.NPcoNP.Source284GraphCanonical
open ComplexityTheory Shared.Beeping
open Shared.ComplexityBridge.CanonicalClasses
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284CanonicalConditional

/-- The graph's source-specific silence condition is exactly the existence
of a single candidate language equal to the full reference complement. -/
theorem eventuallySilent_iff_candidate : target.system.erase.EventuallySilent ↔
    ∃ j, candidateLanguage j = referenceLanguageᶜ := by
  rw [Source284GraphSilence.eventuallySilent_iff]
  exact exists_congr candidate_agrees_iff

/-- Unconditionally, eventual silence of the checked register graph implies
canonical NP = coNP. The proof uses the proved NP membership of every fixed
candidate and the proved completeness of the source reference. -/
theorem eventuallySilent_implies_classes :
    target.system.erase.EventuallySilent → NP = coNP := by
  intro h
  obtain ⟨j,hj⟩ := eventuallySilent_iff_candidate.mp h
  have hc : referenceLanguageᶜ ∈ NP := by
    rw [← hj]
    exact Source284CandidateNP.candidate_mem_NP j
  exact Source284ReferenceHard.reference_complement_iff_classes.mp hc

/-- The converse needs one *fixed* source candidate recognizing the reference
complement whenever that complement lies in NP. This hypothesis does not
assert NP = coNP and cannot vary the candidate with the input. -/
theorem classes_imply_eventuallySilent
    (coverage : referenceLanguageᶜ ∈ NP →
      ∃ j, candidateLanguage j = referenceLanguageᶜ) :
    NP = coNP → target.system.erase.EventuallySilent := by
  intro h
  exact eventuallySilent_iff_candidate.mpr
    (coverage (Source284ReferenceHard.reference_complement_iff_classes.mpr h))

theorem eventuallySilent_iff_classes
    (coverage : referenceLanguageᶜ ∈ NP →
      ∃ j, candidateLanguage j = referenceLanguageᶜ) :
    target.system.erase.EventuallySilent ↔ NP = coNP :=
  ⟨eventuallySilent_implies_classes,classes_imply_eventuallySilent coverage⟩

/-- The exact row-level guard compiler interface suffices for the one
remaining source coverage obligation. The compiler remains unproved. -/
theorem eventuallySilent_iff_classes_of_guardCompiler
    (compiler : Source284GuardCompilerInterface.GuardCompiler) :
    target.system.erase.EventuallySilent ↔ NP = coNP :=
  eventuallySilent_iff_classes (Source284GuardCompilerInterface.coverage_of_guardCompiler compiler)

/-- The same one-way class consequence holds for the checked 15-register
producer before coalescing. -/
theorem producer_eventuallySilent_implies_classes :
    Parent290MaskData.program.system.erase.EventuallySilent → NP = coNP := by
  intro h
  exact eventuallySilent_implies_classes (Parent290Coalesced.eventual_silence_iff.mp h)

end Shared.Beeping.NPcoNP.Source284GraphCanonical
