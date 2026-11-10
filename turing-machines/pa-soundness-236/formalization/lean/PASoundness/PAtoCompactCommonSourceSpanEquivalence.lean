import PASoundness.PAtoCompactCommonSourceSpanInverseWitness
import PASoundness.PAtoCompactCommonSourceSpanGraphWitness

/-! Assemble and eliminate both the restricted-inverse and common-source-span
graph witnesses into the target quotient isomorphism. The common source is an
explicit candidate and the two concrete input matrices remain hypotheses.
This source construction is not an addition-congruence theorem, a PA proof
translation or the PA/machine soundness equivalence. -/
namespace PASoundness.PAtoCompactCommonSourceSpanEquivalence

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactCommonSourceSpanInputMatrices PASoundness.PAtoCompactCommonSourceSpanInverseRestriction
open PASoundness.PAtoCompactCommonSourceSpanComposition PASoundness.PAtoCompactCommonSourceSpanMatrix
open PASoundness.PAtoCompactCommonSourceSpanInverseWitness PASoundness.PAtoCompactCommonSourceSpanGraphWitness

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def matrixGuard : Formula := namedBoth firstMatrix14 (namedBoth secondMatrix (namedCandidate 1))

def targetEquivalent : Formula := replace 1 8 equivalentFormula

private def targetBefore : Formula := replace 1 8 PASoundness.PAtoCompactConditionalTransitivityMatrix.sourceMatrix
private def targetMatrix := PASoundness.PAtoCompactConditionalTransitivityMatrix.targetMatrix
private theorem target_syntax : targetEquivalent.encode = existsCode 6 targetBefore.encode := rfl
private theorem target_renamed : replace 6 9 targetBefore = targetMatrix := rfl

private theorem first_matrix_alignment : firstMatrix14 =
    namedBoth firstBijection14 (replace 6 14 firstOrder) := by decide

/-- With both graph witnesses displayed, package the output isomorphism. -/
def target_of_witnesses : KDerivation (imp matrixGuard.encode
    (imp renamedRestriction.encode (imp spanFull.encode targetEquivalent.encode))) := by
  have hintro := existsIntroduce 9 targetMatrix (by decide)
  have halpha := (existentialAlpha 6 9 targetBefore (by decide) (by decide) (by decide)).2
  rw [target_renamed] at halpha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [spanFull.encode,renamedRestriction.encode,matrixGuard.encode]
  have hs : Context Γ spanFull.encode := .head _ _
  have hr : Context Γ renamedRestriction.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ matrixGuard.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ firstMatrix14.encode := Context.conjunctionLeft hg
  have hsecond : Context Γ secondMatrix.encode := Context.conjunctionLeft (Context.conjunctionRight hg)
  have hm : Context Γ targetMatrix.encode :=
    .mp hs (.mp hr (.mp hsecond (.mp hf (.closed span_isomorphism_matrix))))
  have he9 : Context Γ (existsCode 9 targetMatrix.encode) := .mp hm (.closed hintro)
  have he6 : Context Γ (existsCode 6 targetBefore.encode) := .mp he9 (.closed halpha)
  simpa only [target_syntax] using he6

/-- Construct the two graph witnesses independently from the same source
candidate and two input matrices, then eliminate both into the exact target
isomorphism. Their graph names are fresh and their represented values may
coincide. -/
def common_source_images_equivalent : KDerivation
    (imp firstMatrix14.encode (imp secondMatrix.encode
      (imp (namedCandidate 1).encode targetEquivalent.encode))) := by
  let R : Formula := .imp (.ex 9 spanFull) targetEquivalent
  have hpoint : KDerivation (imp matrixGuard.encode
      (imp renamedRestriction.encode R.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [renamedRestriction.encode,matrixGuard.encode]
    have hr : Context Γ renamedRestriction.encode := .head _ _
    have hg : Context Γ matrixGuard.encode := .hypothesis (by simp [Γ])
    have hl : Context Γ (imp spanFull.encode targetEquivalent.encode) :=
      .mp hr (.mp hg (.closed target_of_witnesses))
    have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 9 h)) := by
      intro h hh
      simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
      by_cases he : h = renamedRestriction.encode
      · subst h; exact free_vacuity 9 renamedRestriction (by decide)
      · have he' : h = matrixGuard.encode := hh.resolve_left he
        subst h; exact free_vacuity 9 matrixGuard (by decide)
    have hall := Context.generalize 9 hv hl
    apply Context.deduction
    exact Context.existsElim (free_vacuity 9 targetEquivalent (by decide))
      (.under hall _) (.head _ _)
  have houter := guarded_exists_left 6 matrixGuard.encode renamedRestriction.encode R.encode
    (free_vacuity 6 matrixGuard (by decide)) (free_vacuity 6 R (by decide)) hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(namedCandidate 1).encode,secondMatrix.encode,firstMatrix14.encode]
  have hc : Context Γ (namedCandidate 1).encode := .head _ _
  have hs : Context Γ secondMatrix.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ firstMatrix14.encode := .hypothesis (by simp [Γ])
  have hguard : Context Γ matrixGuard.encode :=
    Context.conjunctionIntro hf (Context.conjunctionIntro hs hc)
  have hb : Context Γ firstBijection14.encode := by
    have hfirst := hf
    rw [first_matrix_alignment] at hfirst
    exact Context.conjunctionLeft hfirst
  have hinv : Context Γ (existsCode 6 renamedRestriction.encode) :=
    .mp hc (.mp hb (.closed restricted_inverse_exists))
  have hspan : Context Γ (existsCode 9 spanFull.encode) :=
    .mp hc (.mp hs (.mp hf (.closed span_graph_exists)))
  have hr : Context Γ R.encode := .mp hinv (.mp hguard (.closed houter))
  exact .mp hspan hr

theorem common_source_images_equivalent_certificate :
    theoremCode (certificate common_source_images_equivalent) =
      imp firstMatrix14.encode (imp secondMatrix.encode
        (imp (namedCandidate 1).encode targetEquivalent.encode)) :=
  certificate_correct common_source_images_equivalent

end PASoundness.PAtoCompactCommonSourceSpanEquivalence

#print axioms PASoundness.PAtoCompactCommonSourceSpanEquivalence.matrixGuard
#print axioms PASoundness.PAtoCompactCommonSourceSpanEquivalence.targetEquivalent
#print axioms PASoundness.PAtoCompactCommonSourceSpanEquivalence.target_of_witnesses
#print axioms PASoundness.PAtoCompactCommonSourceSpanEquivalence.common_source_images_equivalent
#print axioms PASoundness.PAtoCompactCommonSourceSpanEquivalence.common_source_images_equivalent_certificate
