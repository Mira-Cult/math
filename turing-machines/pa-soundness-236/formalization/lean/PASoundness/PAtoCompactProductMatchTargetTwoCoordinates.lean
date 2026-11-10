import PASoundness.PAtoCompactProductMatchTargetCoordinateUnique

/-! Compare two target coordinate pairs for one output, conditional on an
explicit selected reverse witness. The selected witness is not eliminated. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchTargetTwoCoordinates

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchReverseProduct PASoundness.PAtoCompactProductMatchTargetCoordinateUnique

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def otherCompetitor : Formula := namedBoth (.member 42 60)
  (namedBoth (.member 43 61) (targetTriple 60 61 55))

def other_coordinates_unique : KDerivation
    (imp targetReverseBody.encode (imp otherCompetitor.encode
      (both (equal 60 33) (equal 61 34)))) := by
  have h7 := universalInstance 7 60 (.all 8 uniqueClause) (by decide) (by decide) (by decide)
  have hs7 : replace 7 60 (.all 8 uniqueClause) = .all 8 (replace 7 60 uniqueClause) := by decide
  rw [hs7] at h7
  have h8 := universalInstance 8 61 (replace 7 60 uniqueClause) (by decide) (by decide) (by decide)
  have hs8 : replace 8 61 (replace 7 60 uniqueClause) =
      .imp otherCompetitor (namedBoth (.equal 60 33) (.equal 61 34)) := by decide
  rw [hs8] at h8
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [otherCompetitor.encode,targetReverseBody.encode]
  have hc : Context Γ otherCompetitor.encode := .head _ _
  have hr : Context Γ targetReverseBody.encode := .hypothesis (by simp [Γ])
  have hr' : Context Γ (both (member 42 33) (both (member 43 34)
      (both (targetTriple 33 34 55).encode (allCode 7 (allCode 8 uniqueClause.encode))))) := by
    simpa [reverse_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hr
  have hu := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hr'))
  have hp := Context.mp (Context.mp hu (.closed h7)) (.closed h8)
  simpa [Γ, namedBoth, Formula.not, Formula.encode, both, neg] using Context.mp hc hp

/-- Both competing coordinate pairs are equal via the retained selected pair. -/
def two_coordinates_unique : KDerivation
    (imp targetReverseBody.encode (imp competitor.encode (imp otherCompetitor.encode
      (both (equal 53 60) (equal 54 61))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [otherCompetitor.encode,competitor.encode,targetReverseBody.encode]
  have ho : Context Γ otherCompetitor.encode := .head _ _
  have hc : Context Γ competitor.encode := .hypothesis (by simp [Γ])
  have hr : Context Γ targetReverseBody.encode := .hypothesis (by simp [Γ])
  have h₁ := Context.mp hc (Context.mp hr (.closed target_coordinates_unique))
  have h₂ := Context.mp ho (Context.mp hr (.closed other_coordinates_unique))
  have hm := Context.eqTrans (Context.conjunctionLeft h₁) (Context.eqSymm (Context.conjunctionLeft h₂))
  have hn := Context.eqTrans (Context.conjunctionRight h₁) (Context.eqSymm (Context.conjunctionRight h₂))
  simpa [Γ] using Context.conjunctionIntro hm hn

theorem two_coordinates_unique_certificate : theoremCode (certificate two_coordinates_unique) =
    imp targetReverseBody.encode (imp competitor.encode (imp otherCompetitor.encode
      (both (equal 53 60) (equal 54 61)))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchTargetTwoCoordinates

#print axioms PASoundness.PAtoCompactProductMatchTargetTwoCoordinates.other_coordinates_unique
#print axioms PASoundness.PAtoCompactProductMatchTargetTwoCoordinates.two_coordinates_unique
#print axioms PASoundness.PAtoCompactProductMatchTargetTwoCoordinates.two_coordinates_unique_certificate
