import Shared.Beeping.NPcoNP.Source284PrefixGuardCoverage
import Shared.Beeping.NPcoNP.Source284TaggedWitnessCodec
import Shared.Beeping.NPcoNP.Source284EncodedRows

/-! Source candidate coverage from a tagged bounded-witness verifier.
The verifier, polynomial cutoff, and positive-prefix stability remain
explicit operational hypotheses; no compiler or physical beeper is assumed. -/
namespace Shared.Beeping.NPcoNP.Source284TaggedGuardCoverage

open ComplexityTheory
open Shared.Beeping.NPcoNP.Source284CanonicalConditional
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284RawParse

/-- Tagged counterparts of the existing untagged source-coverage interface.
The two tag bits are explicitly included in the certificate window. The
stability hypothesis permits any proved collection of reject sinks and does
not require a particular internal layout. -/
theorem candidate_of_tagged_stable
    (p cutoff : Polynomial Nat) (R : (List Bool × List Bool) → Bool)
    (description : Nat)
    (hwitness : ∀ i : Nat, (!reference i) = true ↔
      ∃ w : List Bool, w.length ≤ p.eval (2*Source284Parser.length i+1) ∧
        R (payload i.bits,w) = true)
    (hwindow : ∀ i, 0 < Source284Parser.length i →
      Source284WitnessWindow.width (p.eval (2*Source284Parser.length i+1))+2 ≤
        cutoff.eval (Source284Parser.length i))
    (hrealize : ∀ i, 0 < Source284Parser.length i → ∀ c,
      accepts description i c (cutoff.eval (Source284Parser.length i)) =
        Source284TaggedWitnessCodec.check (p.eval (2*Source284Parser.length i+1))
          (fun w => R (payload i.bits,w)) c)
    (hstable : PositiveStableAfter description (fun i => cutoff.eval (Source284Parser.length i)))
    (hfirst : record description 0 < 4) :
    ∃ j, candidateLanguage j = referenceLanguageᶜ := by
  have hcorrect (i : Nat) (hi : 0 < Source284Parser.length i) :
      acceptBound description i (cutoff.eval (Source284Parser.length i))
        (2 ^ cutoff.eval (Source284Parser.length i)) = !reference i := by
    apply Bool.eq_iff_iff.mpr
    rw [acceptBound_iff]
    simp_rw [hrealize i hi]
    rw [Source284TaggedWitnessCodec.clock_search_iff _ _ _ (hwindow i hi)]
    exact (hwitness i).symm
  have hempty (i : Nat) (hi : Source284Parser.length i = 0) :
      acceptBound description i 1 2 = !reference i :=
    Source284EmptyPrefix.empty_first_row description hfirst i hi
  obtain ⟨j,hj⟩ := padded_good_candidate_of_positive_stable description cutoff hstable hcorrect hempty
  exact ⟨j,(candidate_agrees_iff j).1 hj⟩

/-- The exact outstanding uniform tagged-source obligation. The finite row
list and polynomial are fixed for the relation and independent of the tested
input. Stability, the old witness cutoff, alias behavior, and the special
first row are concrete obligations on that same executable source program. -/
def UniformTaggedRealization (p : Polynomial Nat) (R : (List Bool × List Bool) → Bool) : Prop :=
  ∃ (rows : Source284EncodedRows.EncRows) (cutoff : Polynomial Nat),
    0 < rows.length ∧
    Source284ListTables.valid (Source284EncodedRows.decodeRows rows) = true ∧
    let program := Source284ListTables.source (Source284EncodedRows.decodeRows rows)
    record program 0 < 4 ∧
    (∀ i, 0 < Source284Parser.length i →
      Source284WitnessWindow.width (p.eval (2*Source284Parser.length i+1))+2 ≤
        cutoff.eval (Source284Parser.length i)) ∧
    (∀ i, 0 < Source284Parser.length i → ∀ c,
      accepts program i c (cutoff.eval (Source284Parser.length i)) =
        Source284TaggedWitnessCodec.check (p.eval (2*Source284Parser.length i+1))
          (fun w => R (payload i.bits,w)) c) ∧
    PositiveStableAfter program (fun i => cutoff.eval (Source284Parser.length i))

/-- This is an unproved operational obligation, not a complexity axiom or
an assertion that arbitrary Lean functions can be effectively reified. -/
def TaggedGuardCompiler : Prop :=
  ∀ (p : Polynomial Nat) (R : (List Bool × List Bool) → Bool),
    IsPolyTime R → UniformTaggedRealization p R

/-- The fixed-source candidate coverage follows once the stated uniform
finite-table obligation is discharged. -/
theorem coverage_of_tagged_compiler (compiler : TaggedGuardCompiler)
    (hNP : referenceLanguageᶜ ∈ NP) :
    ∃ j, candidateLanguage j = referenceLanguageᶜ := by
  obtain ⟨p,R,hR,hwitness⟩ := Source284PrefixVerifier.witness_of_complement_mem_NP hNP
  obtain ⟨rows,cutoff,_hn,_hv,hfirst,hwindow,hrealize,hstable⟩ := compiler p R hR
  exact candidate_of_tagged_stable p cutoff R
    (Source284ListTables.source (Source284EncodedRows.decodeRows rows))
    hwitness hwindow hrealize hstable hfirst

/-- Conditional endpoint for the shared atomic source controller, not a
theorem about the literal 284-state machine. -/
theorem entry_controller_iff_classes (compiler : TaggedGuardCompiler) :
    (Shared.Beeping.CandidateEntryController.system compare 0).EventuallySilent ↔ NP = coNP :=
  Source284SelectorClosed.entry_controller_iff_classes (coverage_of_tagged_compiler compiler)

end Shared.Beeping.NPcoNP.Source284TaggedGuardCoverage
