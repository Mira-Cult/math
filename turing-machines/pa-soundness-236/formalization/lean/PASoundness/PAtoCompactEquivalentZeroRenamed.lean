import PASoundness.PAtoCompactEquivalentZero
import PASoundness.PAtoCompactConditionalTransitivityWitnessInterface

/-! Capture-safe specialization of the K zero-right isomorphism theorem.
This supplies no quotient transitivity or PA proof interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactEquivalentZeroRenamed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactEquivalentZero PASoundness.PAtoCompactConditionalTransitivityWitnessInterface
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def rightZero : Formula := .all 7 (Formula.member 1 7).not
private def leftZero : Formula := .all 12 (Formula.member 0 12).not
private def source : Formula := rightZero.imp (equivalentFormula.imp leftZero)
private def movedRight : Formula := replace 1 8 source

private def zero_alpha : KDerivation (imp (zeroCode 0 8) (zeroCode 0 12)) := by
  have h := universalAlpha 8 12 ((Formula.member 0 8).not) (by decide) (by decide) (by decide)
  simpa [zeroCode, Formula.not, Formula.encode, replace, rename, neg] using h.1

private def source_proved : KDerivation source.encode := by
  let Z := zeroCode 1 7
  let E := equivalentFormula.encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [E,Z]
  have hz : Context Γ Z := Context.under (Context.head [] Z) E
  have he : Context Γ E := Context.head _ _
  have h := Context.mp he (Context.mp hz (Context.closed equivalent_zero))
  exact Context.mp h (Context.closed zero_alpha)

private def moved_right_proved : KDerivation movedRight.encode := by
  have hi := universalInstance 1 8 source (by decide) (by decide) (by decide)
  exact .mp (.generalize 1 source_proved) hi

/-- A zero graph for object 8 and the literal E(1,8) force a zero graph for
object 1. The original zero binder is renamed 8→12 first; free names 1→8 and
0→1 are then moved in that order, avoiding both capture and identification. -/
def equivalent_zero_renamed : KDerivation
    (imp (zeroCode 8 7) (imp secondEquivalent.encode (zeroCode 1 12))) := by
  have hi := universalInstance 0 1 movedRight (by decide) (by decide) (by decide)
  have h := KDerivation.mp (.generalize 0 moved_right_proved) hi
  simpa [movedRight, source, rightZero, leftZero, replace, rename, Formula.encode,
    Formula.not, zeroCode, neg, secondEquivalent] using h

theorem equivalent_zero_renamed_certificate :
    theoremCode (certificate equivalent_zero_renamed) =
      imp (zeroCode 8 7) (imp secondEquivalent.encode (zeroCode 1 12)) :=
  certificate_correct equivalent_zero_renamed

end PASoundness.PAtoCompactEquivalentZeroRenamed

#print axioms PASoundness.PAtoCompactEquivalentZeroRenamed.equivalent_zero_renamed
#print axioms PASoundness.PAtoCompactEquivalentZeroRenamed.equivalent_zero_renamed_certificate
