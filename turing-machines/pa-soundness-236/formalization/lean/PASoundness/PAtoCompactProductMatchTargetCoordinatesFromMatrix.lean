import PASoundness.PAtoCompactProductMatchTargetTwoCoordinates
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! Target product matrix compares any two supplied coordinate pairs for one
target member. This does not yet compare sources of the match graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchTargetCoordinatesFromMatrix

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchReverseProduct PASoundness.PAtoCompactProductMatchTargetCoordinateUnique
open PASoundness.PAtoCompactProductMatchTargetTwoCoordinates PASoundness.PAtoCompactSuccGraphOutputLift

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def coordinateGuard : Formula := namedBoth competitor otherCompetitor
def coordinateEquality : Formula := namedBoth (.equal 53 60) (.equal 54 61)

def selected_to_equal : KDerivation
    (imp coordinateGuard.encode (imp targetReverseBody.encode coordinateEquality.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [targetReverseBody.encode,coordinateGuard.encode]
  have hr : Context Γ targetReverseBody.encode := .head _ _
  have hg : Context Γ coordinateGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both competitor.encode otherCompetitor.encode) := by
    simpa [coordinateGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have h := Context.mp (Context.conjunctionRight hg') (Context.mp (Context.conjunctionLeft hg')
    (Context.mp hr (.closed two_coordinates_unique)))
  simpa [Γ, coordinateEquality, namedBoth, Formula.not, Formula.encode, both, neg] using h

def target_coordinates_from_matrix : KDerivation (imp targetMatrix.encode (imp (member 44 55)
    (imp coordinateGuard.encode coordinateEquality.encode))) := by
  have h34 := guarded_exists_left 34 coordinateGuard.encode targetReverseBody.encode coordinateEquality.encode
    (coordinateGuard.vacuity 34 (by decide)) (coordinateEquality.vacuity 34 (by decide)) selected_to_equal
  have h33 := guarded_exists_left 33 coordinateGuard.encode (existsCode 34 targetReverseBody.encode) coordinateEquality.encode
    (coordinateGuard.vacuity 33 (by decide)) (coordinateEquality.vacuity 33 (by decide)) h34
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [coordinateGuard.encode,member 44 55,targetMatrix.encode]
  have hg : Context Γ coordinateGuard.encode := .head _ _
  have hy : Context Γ (member 44 55) := .hypothesis (by simp [Γ])
  have hm : Context Γ targetMatrix.encode := .hypothesis (by simp [Γ])
  have hex := Context.mp hy (Context.mp hm (.closed target_coordinates))
  simpa [Γ] using Context.mp hex (Context.mp hg (.closed h33))

theorem target_coordinates_from_matrix_certificate : theoremCode (certificate target_coordinates_from_matrix) =
    imp targetMatrix.encode (imp (member 44 55) (imp coordinateGuard.encode coordinateEquality.encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactProductMatchTargetCoordinatesFromMatrix

#print axioms PASoundness.PAtoCompactProductMatchTargetCoordinatesFromMatrix.selected_to_equal
#print axioms PASoundness.PAtoCompactProductMatchTargetCoordinatesFromMatrix.target_coordinates_from_matrix
#print axioms PASoundness.PAtoCompactProductMatchTargetCoordinatesFromMatrix.target_coordinates_from_matrix_certificate
