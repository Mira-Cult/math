import Shared.Beeping.NPcoNP.Source284PrefixVerifier
import Shared.Beeping.NPcoNP.Source284GuardedSinkCoverage
import Shared.Beeping.NPcoNP.Source284EmptyPrefix

/-! Composition of a concrete source-verifier realization with the proved
prefix witness theorem. This does not construct the verifier, cutoff counter,
reject sink, or physical machine. -/
namespace Shared.Beeping.NPcoNP.Source284PrefixGuardCoverage

open ComplexityTheory
open Shared.Beeping.NPcoNP.Source284CanonicalConditional
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284RawParse

/-- A single source table realizing the normalized verifier at a finite
cutoff, reaching an accepting or stable rejecting state by that cutoff, and
accepting the zero-prefix case in one step, supplies the actual coupled
candidate. The hypotheses are concrete source-table obligations; none states
candidate coverage or a complexity equality. -/
theorem candidate_of_prefix_guard
    (p cutoff : Polynomial Nat) (R : (List Bool × List Bool) → Bool)
    (description sink : Nat)
    (hwitness : ∀ i : Nat, (!reference i) = true ↔
      ∃ w : List Bool, w.length ≤ p.eval (2*Source284Parser.length i+1) ∧
        R (payload i.bits,w) = true)
    (hwindow : ∀ i, 0 < Source284Parser.length i →
      Source284WitnessWindow.width (p.eval (2*Source284Parser.length i+1)) ≤
        cutoff.eval (Source284Parser.length i))
    (hrealize : ∀ i, 0 < Source284Parser.length i → ∀ c,
      accepts description i c (cutoff.eval (Source284Parser.length i)) =
        Source284WitnessWindow.check (p.eval (2*Source284Parser.length i+1))
          (fun w => R (payload i.bits,w)) c)
    (hsinkne : sink ≠ 0)
    (hsink : ∀ c : Config, c.state = sink → (step description c).state = sink)
    (hfinished : ∀ i, 0 < Source284Parser.length i → ∀ c,
      (run description (initial i c) (cutoff.eval (Source284Parser.length i))).state = 0 ∨
      (run description (initial i c) (cutoff.eval (Source284Parser.length i))).state = sink)
    (hfirst : record description 0 < 4) :
    ∃ j, candidateLanguage j = referenceLanguageᶜ := by
  have hcorrect (i : Nat) (hi : 0 < Source284Parser.length i) :
      acceptBound description i (cutoff.eval (Source284Parser.length i))
        (2 ^ cutoff.eval (Source284Parser.length i)) = !reference i := by
    apply Bool.eq_iff_iff.mpr
    rw [acceptBound_iff]
    simp_rw [hrealize i hi]
    rw [Source284WitnessWindow.clock_search_iff _ _ _ (hwindow i hi)]
    exact (hwitness i).symm
  have hempty (i : Nat) (hi : Source284Parser.length i = 0) :
      acceptBound description i 1 2 = !reference i :=
    Source284EmptyPrefix.empty_first_row description hfirst i hi
  obtain ⟨j,hj⟩ := good_candidate_of_sink description sink cutoff hsinkne hsink hfinished hcorrect hempty
  exact ⟨j,(candidate_agrees_iff j).1 hj⟩

end Shared.Beeping.NPcoNP.Source284PrefixGuardCoverage
