import PASoundness.PAtoCompactCommonSourceSpanInversePath
import PASoundness.PAtoCompactConditionalTransitivityPoint

/-! Convert a supplied common-source span graph to the exact restricted
composition condition, given an explicit inverse-graph correspondence. The
paths retain their common witness and the endpoint guards; no candidate
assumption is made on either image object. This does not construct the
inverse graph or prove the resulting graph's isomorphism matrix. -/
namespace PASoundness.PAtoCompactCommonSourceSpanComposition

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCommonSourceSpanBase (spanComposition)
open PASoundness.PAtoCompactCommonSourceSpanInversePath
open PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Full-span invariant with forward input graph moved from name 6 to 14,
leaving name 6 free for its inverse. -/
def spanFull : Formula := replace 6 14 (replace 10 1 spanComposition)

def spanPoint : Formula := .imp (namedBoth (.member 0 2) (.member 8 3))
  (namedBoth (.imp (graphFormula 9 2 3) spanPath)
    (.imp spanPath (graphFormula 9 2 3)))

theorem span_full_syntax : spanFull = .all 2 (.all 3 spanPoint) := by decide

private def span_specialize : KDerivation (imp spanFull.encode spanPoint.encode) := by
  have h2 := allSpecialize 2 (.all 3 spanPoint) (by decide)
  have h3 := allSpecialize 3 spanPoint (by decide)
  have h := compose h2 h3
  simpa only [span_full_syntax, Formula.encode] using h

private def canonicalPath : Formula := PASoundness.PAtoCompactConditionalTransitivityPoint.path
private def canonicalPoint : Formula := PASoundness.PAtoCompactConditionalTransitivityPoint.point
private def canonicalComposition : Formula := PASoundness.PAtoCompactConditionalTransitivityPoint.composition

private theorem composite_body_alpha : replace 4 10 compositeBody =
    PASoundness.PAtoCompactConditionalTransitivityPoint.pathBody := by decide

private def path_alpha_forward : KDerivation (imp compositePath.encode canonicalPath.encode) := by
  have h := (existentialAlpha 4 10 compositeBody (by decide) (by decide) (by decide)).1
  rw [composite_body_alpha] at h
  simpa only [compositePath, canonicalPath, PASoundness.PAtoCompactConditionalTransitivityPoint.path,
    Formula.encode] using h

private def path_alpha_backward : KDerivation (imp canonicalPath.encode compositePath.encode) := by
  have h := (existentialAlpha 4 10 compositeBody (by decide) (by decide) (by decide)).2
  rw [composite_body_alpha] at h
  simpa only [compositePath, canonicalPath, PASoundness.PAtoCompactConditionalTransitivityPoint.path,
    Formula.encode] using h

def transferGuard : Formula := namedBoth inverseCorrespondence spanFull

/-- An explicitly supplied inverse correspondence and common-source span
graph entail the exact endpoint-restricted composition graph condition. -/
def span_to_composition : KDerivation
    (imp inverseCorrespondence.encode (imp spanFull.encode canonicalComposition.encode)) := by
  let Γ := [transferGuard.encode]
  have hg : Context Γ transferGuard.encode := .head _ _
  have hi : Context Γ inverseCorrespondence.encode := Context.conjunctionLeft hg
  have hs : Context Γ spanFull.encode := Context.conjunctionRight hg
  have hpoint : Context Γ canonicalPoint.encode := by
    apply Context.deduction
    let D := both (member 0 2) (member 8 3)
    let Δ := [D,transferGuard.encode]
    have hd : Context Δ D := .head _ _
    have hx : Context Δ (member 0 2) := Context.conjunctionLeft hd
    have hsg : Context Δ (both (imp (graphFormula 9 2 3).encode spanPath.encode)
        (imp spanPath.encode (graphFormula 9 2 3).encode)) := by
      have hp : Context Δ spanPoint.encode := .mp (.under hs _) (.closed span_specialize)
      exact .mp hd hp
    have hpg : Context Δ pathGuard.encode := Context.conjunctionIntro (.under hi _) hx
    have hforward : Context Δ (imp (graphFormula 9 2 3).encode canonicalPath.encode) := by
      apply Context.deduction
      let Θ := (graphFormula 9 2 3).encode :: Δ
      have he : Context Θ (graphFormula 9 2 3).encode := .head _ _
      have hspan : Context Θ spanPath.encode := .mp he (Context.conjunctionLeft (.under hsg _))
      have hcomp : Context Θ compositePath.encode :=
        .mp hspan (.mp (.under hpg _) (.closed span_to_composite))
      exact .mp hcomp (.closed path_alpha_forward)
    have hbackward : Context Δ (imp canonicalPath.encode (graphFormula 9 2 3).encode) := by
      apply Context.deduction
      let Θ := canonicalPath.encode :: Δ
      have hc : Context Θ canonicalPath.encode := .head _ _
      have hcomp : Context Θ compositePath.encode := .mp hc (.closed path_alpha_backward)
      have hspan : Context Θ spanPath.encode :=
        .mp hcomp (.mp (.under hpg _) (.closed composite_to_span))
      exact .mp hspan (Context.conjunctionRight (.under hsg _))
    exact Context.conjunctionIntro hforward hbackward
  have hv3 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 3 h)) := by
    intro h hh
    have he : h = transferGuard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 3 transferGuard (by decide)
  have hv2 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    have he : h = transferGuard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 2 transferGuard (by decide)
  have hall : Context Γ canonicalComposition.encode := by
    simpa only [canonicalComposition, canonicalPoint,
      PASoundness.PAtoCompactConditionalTransitivityPoint.composition, Formula.encode] using
      Context.generalize 2 hv2 (Context.generalize 3 hv3 hpoint)
  have hguard : KDerivation (imp transferGuard.encode canonicalComposition.encode) :=
    Context.closeEmpty (Context.deduction hall)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Δ := [spanFull.encode,inverseCorrespondence.encode]
  have hs : Context Δ spanFull.encode := .head _ _
  have hi : Context Δ inverseCorrespondence.encode := .hypothesis (by simp [Δ])
  have hg : Context Δ transferGuard.encode := Context.conjunctionIntro hi hs
  exact .mp hg (.closed hguard)

theorem span_to_composition_certificate : theoremCode (certificate span_to_composition) =
    imp inverseCorrespondence.encode (imp spanFull.encode canonicalComposition.encode) :=
  certificate_correct span_to_composition

end PASoundness.PAtoCompactCommonSourceSpanComposition

#print axioms PASoundness.PAtoCompactCommonSourceSpanComposition.spanFull
#print axioms PASoundness.PAtoCompactCommonSourceSpanComposition.spanPoint
#print axioms PASoundness.PAtoCompactCommonSourceSpanComposition.span_full_syntax
#print axioms PASoundness.PAtoCompactCommonSourceSpanComposition.transferGuard
#print axioms PASoundness.PAtoCompactCommonSourceSpanComposition.span_to_composition
#print axioms PASoundness.PAtoCompactCommonSourceSpanComposition.span_to_composition_certificate
