import PASoundness.PAtoCompactProductMatchPointOrder
import PASoundness.PAtoCompactProductMatchPathUnique

/-! Pointwise order comparison for two explicit product-matching paths.
Both product matrices, both factor-order clauses, the first factor bijection,
source-output membership and both complete path bodies remain antecedents.
This is not yet the quantified order clause for a represented match graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchPathOrderPoint

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductMatchFactorOrderPoint PASoundness.PAtoCompactProductMatchFactorEquality
open PASoundness.PAtoCompactProductMatchTargetOutput PASoundness.PAtoCompactProductMatchPointUnique
open PASoundness.PAtoCompactProductMatchPointWitness
open PASoundness.PAtoCompactProductMatchSourceWitness PASoundness.PAtoCompactProductMatchPathUnique
open PASoundness.PAtoCompactProductMatchBothImages PASoundness.PAtoCompactProductMatchTargetWitness
open PASoundness.PAtoCompactProductMatchPointOrder PASoundness.PAtoCompactProductIsoPointwiseLex

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def otherBody : Formula := replace 32 52 rivalMatchBody
def otherReverse : Formula := replace 32 52 rivalReverse
def otherReverseTail : Formula := .all 7 (.all 8
  (replace 32 52 (replace 31 51 (replace 30 50 reverseUnique))))

theorem other_body_shape : otherBody = namedBoth otherReverse
    (namedBoth (namedBoth rivalFirst rivalSecond) rivalTarget) := by decide
theorem other_reverse_shape : otherReverse = namedBoth (.member 0 50)
    (namedBoth (.member 1 51) (namedBoth (tripleFormula 50 51 52) otherReverseTail)) := by decide

def guard : Formula := namedBoth productMatrix (namedBoth targetMatrix
  (namedBoth firstBijection (namedBoth firstOrder (namedBoth secondOrder
    (namedBoth (.member 2 32) (.member 2 52))))))

/-- From the two explicit matching paths, reconstruct the exact guards of
the reviewed pointwise product-order constructor. -/
def path_point_order : KDerivation (imp guard.encode (imp retainedMatchBody.encode
    (imp otherBody.encode (iffCode (member 52 32) (member 55 35))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [otherBody.encode,retainedMatchBody.encode,guard.encode]
  have ho : Context Γ otherBody.encode := .head _ _
  have hp : Context Γ retainedMatchBody.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ guard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both productMatrix.encode (both targetMatrix.encode
      (both firstBijection.encode (both firstOrder.encode (both secondOrder.encode
        (both (member 2 32) (member 2 52))))))) := by
    simpa [guard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have hmain : Context Γ (both selectedReverseBody.encode
      (both (both firstImage.encode secondImage.encode) targetOutputBody.encode)) := by
    simpa [retainedMatchBody, matchBody, bothImages, namedBoth, Formula.not,
      Formula.encode, both, neg] using hp
  have hother : Context Γ (both otherReverse.encode
      (both (both rivalFirst.encode rivalSecond.encode) rivalTarget.encode)) := by
    simpa [other_body_shape, namedBoth, Formula.not, Formula.encode, both, neg] using ho
  have hpM := Context.conjunctionLeft hg'
  have htM := Context.conjunctionLeft (Context.conjunctionRight hg')
  have hb := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg'))
  have ho₁ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))
  have ho₂ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg'))))
  have hout := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg'))))
  have h32 := Context.conjunctionLeft hout
  have h52 := Context.conjunctionRight hout
  have hr₁ := Context.conjunctionLeft hmain
  have hi₁ := Context.conjunctionLeft (Context.conjunctionLeft (Context.conjunctionRight hmain))
  have hj₁ := Context.conjunctionRight (Context.conjunctionLeft (Context.conjunctionRight hmain))
  have ht₁ := Context.conjunctionRight (Context.conjunctionRight hmain)
  have hr₂ := Context.conjunctionLeft hother
  have hi₂ := Context.conjunctionLeft (Context.conjunctionLeft (Context.conjunctionRight hother))
  have hj₂ := Context.conjunctionRight (Context.conjunctionLeft (Context.conjunctionRight hother))
  have ht₂ := Context.conjunctionRight (Context.conjunctionRight hother)
  have hr₁' : Context Γ (both (member 0 30) (both (member 1 31)
      (both (tripleFormula 30 31 32).encode (allCode 7 (allCode 8 reverseUnique.encode))))) := by
    simpa [reverse_selected_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hr₁
  have hr₂' : Context Γ (both (member 0 50) (both (member 1 51)
      (both (tripleFormula 50 51 52).encode otherReverseTail.encode))) := by
    simpa [other_reverse_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hr₂
  have hi₁' : Context Γ (both (member 42 33) (both (graphFormula 40 30 33).encode
      (Formula.all 4 (.imp (namedBoth (.member 42 4) (graphFormula 40 30 4)) (.equal 4 33))).encode)) := by
    simpa [firstImage, namedBoth, Formula.not, Formula.encode, both, neg] using hi₁
  have hi₂' : Context Γ (both (member 42 53) (both (graphFormula 40 50 53).encode
      (Formula.all 4 (.imp (namedBoth (.member 42 4) (graphFormula 40 50 4)) (.equal 4 53))).encode)) := by
    simpa [rival_first_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hi₂
  have hj₁' : Context Γ (both (member 43 34) (both (graphFormula 41 31 34).encode
      (Formula.all 4 (.imp (namedBoth (.member 43 4) (graphFormula 41 31 4)) (.equal 4 34))).encode)) := by
    simpa [secondImage, namedBoth, Formula.not, Formula.encode, both, neg] using hj₁
  have hj₂' : Context Γ (both (member 43 54) (both (graphFormula 41 51 54).encode
      (Formula.all 4 (.imp (namedBoth (.member 43 4) (graphFormula 41 51 4)) (.equal 4 54))).encode)) := by
    simpa [rival_second_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hj₂
  have ht₁' : Context Γ (both (member 44 35) (both (targetTriple 33 34 35).encode
      (Formula.all 9 (.imp (namedBoth (.member 44 9) (targetTriple 33 34 9)) (.equal 9 35))).encode)) := by
    simpa [targetOutputBody, namedBoth, Formula.not, Formula.encode, both, neg] using ht₁
  have ht₂' : Context Γ (both (member 44 55) (both (targetTriple 53 54 55).encode
      (Formula.all 9 (.imp (namedBoth (.member 44 9) (targetTriple 53 54 9)) (.equal 9 55))).encode)) := by
    simpa [rival_target_shape, namedBoth, Formula.not, Formula.encode, both, neg] using ht₂
  have hx₁ := Context.conjunctionLeft hr₁'
  have hy₁ := Context.conjunctionLeft (Context.conjunctionRight hr₁')
  have hz₁ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hr₁'))
  have hx₂ := Context.conjunctionLeft hr₂'
  have hy₂ := Context.conjunctionLeft (Context.conjunctionRight hr₂')
  have hz₂ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hr₂'))
  have ha₁ := Context.conjunctionLeft hi₁'
  have ha₂ := Context.conjunctionLeft hi₂'
  have hb₁ := Context.conjunctionLeft hj₁'
  have hb₂ := Context.conjunctionLeft hj₂'
  have hg₁ := Context.conjunctionLeft (Context.conjunctionRight hi₁')
  have hg₂ := Context.conjunctionLeft (Context.conjunctionRight hi₂')
  have hh₁ := Context.conjunctionLeft (Context.conjunctionRight hj₁')
  have hh₂ := Context.conjunctionLeft (Context.conjunctionRight hj₂')
  have hc₁ := Context.conjunctionLeft ht₁'
  have hc₂ := Context.conjunctionLeft ht₂'
  have ht₁e := Context.conjunctionLeft (Context.conjunctionRight ht₁')
  have ht₂e := Context.conjunctionLeft (Context.conjunctionRight ht₂')
  have hsource : Context Γ sourceGuard.encode := by
    have h := Context.conjunctionIntro hx₁ (Context.conjunctionIntro hy₁
      (Context.conjunctionIntro h32 (Context.conjunctionIntro hx₂ (Context.conjunctionIntro hy₂
        (Context.conjunctionIntro h52 (Context.conjunctionIntro hz₁ hz₂))))))
    simpa [sourceGuard, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have htarget : Context Γ targetGuard.encode := by
    have h := Context.conjunctionIntro ha₁ (Context.conjunctionIntro hb₁
      (Context.conjunctionIntro hc₁ (Context.conjunctionIntro ha₂ (Context.conjunctionIntro hb₂
        (Context.conjunctionIntro hc₂ (Context.conjunctionIntro ht₁e ht₂e))))))
    simpa [targetGuard, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hfirst : Context Γ firstGuard.encode := by
    have h := Context.conjunctionIntro hx₁ (Context.conjunctionIntro hx₂
      (Context.conjunctionIntro ha₁ (Context.conjunctionIntro ha₂ (Context.conjunctionIntro hg₁ hg₂))))
    simpa [firstGuard, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hsecond : Context Γ secondGuard.encode := by
    have h := Context.conjunctionIntro hy₁ (Context.conjunctionIntro hy₂
      (Context.conjunctionIntro hb₁ (Context.conjunctionIntro hb₂ (Context.conjunctionIntro hh₁ hh₂))))
    simpa [secondGuard, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hequality : Context Γ factorGuard.encode := by
    have h := Context.conjunctionIntro hb (Context.conjunctionIntro hx₁
      (Context.conjunctionIntro hx₂ (Context.conjunctionIntro hi₁ hi₂)))
    simpa [factorGuard, otherImage, rivalFirst, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hall : Context Γ assumptions.encode := by
    have h := Context.conjunctionIntro hpM (Context.conjunctionIntro htM
      (Context.conjunctionIntro ho₁ (Context.conjunctionIntro ho₂ (Context.conjunctionIntro hequality
        (Context.conjunctionIntro hsource (Context.conjunctionIntro htarget
          (Context.conjunctionIntro hfirst hsecond)))))))
    simpa [assumptions, namedBoth, Formula.not, Formula.encode, both, neg] using h
  exact .mp hall (.closed matched_point_order)

theorem path_point_order_certificate : theoremCode (certificate path_point_order) =
    imp guard.encode (imp retainedMatchBody.encode
      (imp otherBody.encode (iffCode (member 52 32) (member 55 35)))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchPathOrderPoint

#print axioms PASoundness.PAtoCompactProductMatchPathOrderPoint.path_point_order
#print axioms PASoundness.PAtoCompactProductMatchPathOrderPoint.path_point_order_certificate
