import PASoundness.PAtoCompactCommonSourceSpanBackward

/-! Quantified common-source span successor with supplied selected images and
supplied pair/adjunction witnesses. Pointwise forward and backward K proofs
are combined and quantified over both image endpoints. This module does not
yet construct or eliminate the image/pair/graph witnesses or prove induction. -/
namespace PASoundness.PAtoCompactCommonSourceSpanStep

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCommonSourceSpanBase PASoundness.PAtoCompactCommonSourceSpanImages
open PASoundness.PAtoCompactCommonSourceSpanSelectedStep PASoundness.PAtoCompactCommonSourceSpanForward
open PASoundness.PAtoCompactCommonSourceSpanBackward PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Old invariant, both selected image witnesses, common-source membership,
successor prefix, and the supplied pair and graph adjunction. -/
def stepGuard : Formula := namedBoth spanComposition
  (namedBoth firstImageBody (namedBoth secondImageBody
    (namedBoth (.member 1 10) (namedBoth (namedSuccessor 10 13 15)
      (namedBoth (pairFormula 16 11 12) (namedAdjoin 9 16 17 18))))))

private def nextPoint : Formula := .imp (namedBoth (.member 0 2) (.member 8 3))
  (namedBoth (.imp (graphFormula 17 2 3) successorPath)
    (.imp successorPath (graphFormula 17 2 3)))

/-- The next invariant uses the same image objects and input graphs, successor
prefix 13, and the adjoined output graph 17. -/
def nextSpan : Formula := .all 2 (.all 3 nextPoint)

/-- Construct the full pointwise-and-quantified next invariant from explicit
old invariant, image witnesses and pair/adjunction hypotheses. -/
def supplied_span_successor : KDerivation (imp stepGuard.encode nextSpan.encode) := by
  let Γ := [stepGuard.encode]
  have hg : Context Γ stepGuard.encode := .head _ _
  have hi : Context Γ spanComposition.encode := Context.conjunctionLeft hg
  have hg := Context.conjunctionRight hg
  have hf : Context Γ firstImageBody.encode := Context.conjunctionLeft hg
  have hg := Context.conjunctionRight hg
  have hs : Context Γ secondImageBody.encode := Context.conjunctionLeft hg
  have hg := Context.conjunctionRight hg
  have hm : Context Γ (member 1 10) := Context.conjunctionLeft hg
  have hg := Context.conjunctionRight hg
  have hsucc : Context Γ (successorCode 10 13 15) := Context.conjunctionLeft hg
  have hg := Context.conjunctionRight hg
  have hp : Context Γ (pairFormula 16 11 12).encode := Context.conjunctionLeft hg
  have ha : Context Γ (adjoinCode 9 16 17 18) := Context.conjunctionRight hg
  have hfedge : Context Γ (graphFormula 6 10 11).encode :=
    Context.conjunctionLeft (Context.conjunctionRight hf)
  have hsedge : Context Γ (graphFormula 7 10 12).encode :=
    Context.conjunctionLeft (Context.conjunctionRight hs)
  have hpoint : Context Γ nextPoint.encode := by
    apply Context.deduction
    let D := both (member 0 2) (member 8 3)
    let Δ := [D,stepGuard.encode]
    have hdomain : Context Δ D := .head _ _
    have hx : Context Δ (member 0 2) := Context.conjunctionLeft hdomain
    have hy : Context Δ (member 8 3) := Context.conjunctionRight hdomain
    have hforward : Context Δ (imp (graphFormula 17 2 3).encode successorPath.encode) :=
      .mp (.under ha _) (.mp (.under hp _) (.mp (.under hsedge _) (.mp (.under hfedge _)
        (.mp (.under hsucc _) (.mp (.under hm _) (.mp hy (.mp hx (.mp (.under hi _) (.closed forward_point)))))))))
    have hreverseGuard : Context Δ reverseGuard.encode :=
      Context.conjunctionIntro (.under hi _) (Context.conjunctionIntro (.under hf _)
        (Context.conjunctionIntro (.under hs _) (Context.conjunctionIntro (.under hsucc _)
          (Context.conjunctionIntro hx (Context.conjunctionIntro hy
            (Context.conjunctionIntro (.under hp _) (.under ha _)))))))
    have hback : Context Δ (imp successorPath.encode (graphFormula 17 2 3).encode) :=
      .mp hreverseGuard (.closed backward_point)
    exact Context.conjunctionIntro hforward hback
  have hv3 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 3 h)) := by
    intro h hh
    have he : h = stepGuard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 3 stepGuard (by decide)
  have hv2 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    have he : h = stepGuard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 2 stepGuard (by decide)
  have hall : Context Γ nextSpan.encode := by
    simpa only [nextSpan, Formula.encode] using
      Context.generalize 2 hv2 (Context.generalize 3 hv3 hpoint)
  exact Context.closeEmpty (Context.deduction hall)

theorem supplied_span_successor_certificate :
    theoremCode (certificate supplied_span_successor) = imp stepGuard.encode nextSpan.encode :=
  certificate_correct supplied_span_successor

end PASoundness.PAtoCompactCommonSourceSpanStep

#print axioms PASoundness.PAtoCompactCommonSourceSpanStep.stepGuard
#print axioms PASoundness.PAtoCompactCommonSourceSpanStep.nextSpan
#print axioms PASoundness.PAtoCompactCommonSourceSpanStep.supplied_span_successor
#print axioms PASoundness.PAtoCompactCommonSourceSpanStep.supplied_span_successor_certificate
