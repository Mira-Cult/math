import PASoundness.PAtoCompactMultiplicationCanonicalBaseStep
import PASoundness.PAtoCompactProductAllocatedRaw303132
import PASoundness.PAtoCompactAnchoredProductWitnessClosed
import PASoundness.PAtoCompactAnchoredForwardWitnessWithLex

/-! Assemble the literal canonical product-successor goal from a supplied
finite K proof eliminating the same retained suffix/map/row witnesses into
the new raw product. The retained-witness elimination is an explicit proof
input here: this module alone proves neither multiplication totality nor PA
soundness. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCanonicalFromRetained
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.PAtoCompactMultiplicationCanonicalBaseStep
open PASoundness.PAtoCompactProductAllocatedRaw303132
open PASoundness.PAtoCompactAnchoredProductWitnessPackage
open PASoundness.PAtoCompactAnchoredProductWitnessClosed
open PASoundness.PAtoCompactAnchoredForwardWitnessLift
open PASoundness.PAtoCompactAnchoredForwardWitnessWithLex
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- If the retained same-witness package yields the new raw product in K,
then the exact canonical first-factor successor step follows. -/
noncomputable def canonical_from_retained
    (finish : KDerivation (imp retainedLexResult rawNew.encode)) :
    KDerivation canonical100.encode := by
  let D (x : Nat) := (domainAt 100 x).encode
  let S := (namedSuccessor 30 38 39).encode
  let O := rawOld.encode
  let C := (literalCutAt 100 32 31 45).encode
  change KDerivation (imp (D 30) (imp (D 31) (imp (D 32)
    (imp S (imp (D 38) (imp O (imp (D 45) (imp C rawNew.encode))))))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [C,D 45,O,D 38,S,D 32,D 31,D 30]
  have h30 : Context Γ (D 30) := .hypothesis (by simp [Γ])
  have h31 : Context Γ (D 31) := .hypothesis (by simp [Γ])
  have h32 : Context Γ (D 32) := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have h45 : Context Γ (D 45) := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .head _ _
  have hallocated : Context Γ (mulAt 100 30 31 32).encode := by
    exact .mp ho (.closed raw_to_allocated)
  have hi : Context Γ inputs.encode := by
    have hh := Context.conjunctionIntro hallocated h31
    simpa [inputs,namedBoth,Formula.not,Formula.encode,both,neg,D] using hh
  have hg : Context Γ guards.encode := by
    have hh := Context.conjunctionIntro h30
      (Context.conjunctionIntro h32 (Context.conjunctionIntro h45 hs))
    simpa [guards,namedBoth,Formula.not,Formula.encode,both,neg,D,S] using hh
  have hw : Context Γ anchoredResult.encode :=
    .mp hi (.mp hc (.closed anchored_product_witness))
  have hr : Context Γ retainedLexResult :=
    .mp hw (.mp hg (.closed retain_forward_with_lex))
  exact .mp hr (.closed finish)

theorem canonical_from_retained_certificate
    (finish : KDerivation (imp retainedLexResult rawNew.encode)) :
    theoremCode (certificate (canonical_from_retained finish)) = canonical100.encode :=
  certificate_correct _
end PASoundness.PAtoCompactMultiplicationCanonicalFromRetained
#print axioms PASoundness.PAtoCompactMultiplicationCanonicalFromRetained.canonical_from_retained
#print axioms PASoundness.PAtoCompactMultiplicationCanonicalFromRetained.canonical_from_retained_certificate
