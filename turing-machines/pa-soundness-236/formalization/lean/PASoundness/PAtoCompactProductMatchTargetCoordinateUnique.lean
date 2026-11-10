import PASoundness.PAtoCompactProductMatchReverseReconstruct

/-! Compare a selected target-product reverse witness with another pair of
target coordinates for the same output. This is not yet reverse uniqueness
of the represented match graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchTargetCoordinateUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchReverseProduct PASoundness.PAtoCompactProductMatchReverseReconstruct

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def uniqueClause : Formula := .imp
  (namedBoth (.member 42 7) (namedBoth (.member 43 8) (targetTriple 7 8 55)))
  (namedBoth (.equal 7 33) (.equal 8 34))
def competitor : Formula := namedBoth (.member 42 53)
  (namedBoth (.member 43 54) (targetTriple 53 54 55))

theorem reverse_shape : targetReverseBody = namedBoth (.member 42 33)
    (namedBoth (.member 43 34) (namedBoth (targetTriple 33 34 55)
      (.all 7 (.all 8 uniqueClause)))) := by decide

def target_coordinates_unique : KDerivation
    (imp targetReverseBody.encode (imp competitor.encode
      (both (equal 53 33) (equal 54 34)))) := by
  have h7 := universalInstance 7 53 (.all 8 uniqueClause) (by decide) (by decide) (by decide)
  have hs7 : replace 7 53 (.all 8 uniqueClause) = .all 8 (replace 7 53 uniqueClause) := by decide
  rw [hs7] at h7
  have h8 := universalInstance 8 54 (replace 7 53 uniqueClause) (by decide) (by decide) (by decide)
  have hs8 : replace 8 54 (replace 7 53 uniqueClause) =
      .imp competitor (namedBoth (.equal 53 33) (.equal 54 34)) := by decide
  rw [hs8] at h8
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [competitor.encode,targetReverseBody.encode]
  have hc : Context Γ competitor.encode := .head _ _
  have hr : Context Γ targetReverseBody.encode := .hypothesis (by simp [Γ])
  have hr' : Context Γ (both (member 42 33) (both (member 43 34)
      (both (targetTriple 33 34 55).encode (allCode 7 (allCode 8 uniqueClause.encode))))) := by
    simpa [reverse_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hr
  have hu := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hr'))
  have hp := Context.mp (Context.mp hu (.closed h7)) (.closed h8)
  simpa [Γ, namedBoth, Formula.not, Formula.encode, both, neg] using Context.mp hc hp

theorem target_coordinates_unique_certificate : theoremCode (certificate target_coordinates_unique) =
    imp targetReverseBody.encode (imp competitor.encode (both (equal 53 33) (equal 54 34))) :=
  certificate_correct _

end PASoundness.PAtoCompactProductMatchTargetCoordinateUnique

#print axioms PASoundness.PAtoCompactProductMatchTargetCoordinateUnique.target_coordinates_unique
#print axioms PASoundness.PAtoCompactProductMatchTargetCoordinateUnique.target_coordinates_unique_certificate
