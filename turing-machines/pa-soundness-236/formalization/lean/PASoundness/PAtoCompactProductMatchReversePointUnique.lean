import PASoundness.PAtoCompactProductMatchTargetPathCoordinates
import PASoundness.PAtoCompactProductMatchMinorFactorReflection
import PASoundness.PAtoCompactProductMatchSourceOutputUnique
import PASoundness.PAtoCompactProductMatchPathOrderPoint
import PASoundness.PAtoCompactProductMatchReverseReconstruct

/-! Two explicit matching bodies at the same target have equal source outputs,
under both product matrices, both factor bijections and endpoint memberships. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchReversePointUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductMatchPointWitness
open PASoundness.PAtoCompactProductMatchPointUnique PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductMatchFactorEquality PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchPathUnique PASoundness.PAtoCompactProductMatchPathOrderPoint
open PASoundness.PAtoCompactProductMatchReverseReconstruct PASoundness.PAtoCompactProductMatchTargetWitnessFromEdge
open PASoundness.PAtoCompactProductMatchTargetPathCoordinates PASoundness.PAtoCompactProductMatchMinorFactorReflection
open PASoundness.PAtoCompactProductMatchSourceOutputUnique

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def assumptions : Formula := namedBoth productMatrix (namedBoth targetMatrix
  (namedBoth firstBijection (namedBoth secondBijection
    (namedBoth (.member 2 32) (namedBoth (.member 2 52) (.member 44 55))))))

theorem first_target_shape : target55 = namedBoth (.member 44 55)
    (namedBoth (targetTriple 33 34 55) (.all 9
      (.imp (namedBoth (.member 44 9) (targetTriple 33 34 9)) (.equal 9 55)))) := by decide

theorem minor_guard_shape : minorGuard = namedBoth secondBijection (namedBoth (.member 1 31)
    (namedBoth (.member 1 51) (namedBoth secondImage rivalSecond))) := by decide

def reverse_point_unique : KDerivation (imp assumptions.encode
    (imp pathBody55.encode (imp otherBody.encode (equal 32 52)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [otherBody.encode,pathBody55.encode,assumptions.encode]
  have ho : Context Γ otherBody.encode := .head _ _
  have hp : Context Γ pathBody55.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both productMatrix.encode (both targetMatrix.encode
      (both firstBijection.encode (both secondBijection.encode
        (both (member 2 32) (both (member 2 52) (member 44 55))))))) := by
    simpa [assumptions, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have hp' : Context Γ (both selectedReverseBody.encode
      (both (both firstImage.encode secondImage.encode) target55.encode)) := by
    simpa [path_body_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hp
  have ho' : Context Γ (both otherReverse.encode
      (both (both rivalFirst.encode rivalSecond.encode) rivalTarget.encode)) := by
    simpa [other_body_shape, namedBoth, Formula.not, Formula.encode, both, neg] using ho
  have hpm := Context.conjunctionLeft hg'
  have htm := Context.conjunctionLeft (Context.conjunctionRight hg')
  have hb₁ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg'))
  have hb₂ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))
  have hmem := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))
  have h32 := Context.conjunctionLeft hmem
  have h52 := Context.conjunctionLeft (Context.conjunctionRight hmem)
  have h55 := Context.conjunctionRight (Context.conjunctionRight hmem)
  have hr₁ := Context.conjunctionLeft hp'
  have hi₁ := Context.conjunctionLeft (Context.conjunctionLeft (Context.conjunctionRight hp'))
  have hj₁ := Context.conjunctionRight (Context.conjunctionLeft (Context.conjunctionRight hp'))
  have ht₁ := Context.conjunctionRight (Context.conjunctionRight hp')
  have hr₂ := Context.conjunctionLeft ho'
  have hi₂ := Context.conjunctionLeft (Context.conjunctionLeft (Context.conjunctionRight ho'))
  have hj₂ := Context.conjunctionRight (Context.conjunctionLeft (Context.conjunctionRight ho'))
  have ht₂ := Context.conjunctionRight (Context.conjunctionRight ho')
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
  have ht₁' : Context Γ (both (member 44 55) (both (targetTriple 33 34 55).encode
      (Formula.all 9 (.imp (namedBoth (.member 44 9) (targetTriple 33 34 9)) (.equal 9 55))).encode)) := by
    simpa [first_target_shape, namedBoth, Formula.not, Formula.encode, both, neg] using ht₁
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
  have hb₁' := Context.conjunctionLeft hj₁'
  have hb₂' := Context.conjunctionLeft hj₂'
  have ht₁e := Context.conjunctionLeft (Context.conjunctionRight ht₁')
  have ht₂e := Context.conjunctionLeft (Context.conjunctionRight ht₂')
  have htguard : Context Γ pathGuard.encode := by
    have h := Context.conjunctionIntro (Context.conjunctionIntro ha₁ (Context.conjunctionIntro hb₁' ht₁e))
      (Context.conjunctionIntro ha₂ (Context.conjunctionIntro hb₂' ht₂e))
    simpa [pathGuard, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hte : Context Γ pathEquality.encode :=
    .mp htguard (.mp h55 (.mp htm (.closed target_path_coordinates_unique)))
  have hte' : Context Γ (both (equal 33 53) (equal 34 54)) := by
    simpa [pathEquality, namedBoth, Formula.not, Formula.encode, both, neg] using hte
  have hmajor : Context Γ factorGuard.encode := by
    have h := Context.conjunctionIntro hb₁ (Context.conjunctionIntro hx₁
      (Context.conjunctionIntro hx₂ (Context.conjunctionIntro hi₁ hi₂)))
    simpa [factorGuard, otherImage, rivalFirst, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hminor : Context Γ minorGuard.encode := by
    have h := Context.conjunctionIntro hb₂ (Context.conjunctionIntro hy₁
      (Context.conjunctionIntro hy₂ (Context.conjunctionIntro hj₁ hj₂)))
    simpa [minor_guard_shape, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have he₁ : Context Γ (equal 30 50) := .mp (Context.conjunctionLeft hte') (.mp hmajor (.closed reflects_equality))
  have he₂ : Context Γ (equal 31 51) := .mp (Context.conjunctionRight hte') (.mp hminor (.closed minor_reflects_equality))
  have hs : Context Γ PASoundness.PAtoCompactProductMatchSourceOutputUnique.sourceGuard.encode := by
    have h := Context.conjunctionIntro hpm (Context.conjunctionIntro hx₁ (Context.conjunctionIntro hy₁
      (Context.conjunctionIntro h32 (Context.conjunctionIntro h52
        (Context.conjunctionIntro hz₁ (Context.conjunctionIntro hz₂ (Context.conjunctionIntro he₁ he₂)))))))
    simpa [PASoundness.PAtoCompactProductMatchSourceOutputUnique.sourceGuard,
      namedBoth, Formula.not, Formula.encode, both, neg] using h
  simpa [Γ] using Context.mp hs (.closed source_outputs_equal)

theorem reverse_point_unique_certificate : theoremCode (certificate reverse_point_unique) =
    imp assumptions.encode (imp pathBody55.encode (imp otherBody.encode (equal 32 52))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchReversePointUnique

#print axioms PASoundness.PAtoCompactProductMatchReversePointUnique.reverse_point_unique
#print axioms PASoundness.PAtoCompactProductMatchReversePointUnique.reverse_point_unique_certificate
