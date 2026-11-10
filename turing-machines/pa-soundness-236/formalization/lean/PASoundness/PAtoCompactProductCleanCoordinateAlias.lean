import PASoundness.PAtoCompactKuratowskiInjectivity
import PASoundness.CompactNamed

/-! Literal K coordinate comparison for a queried product edge and an
explicit cleanliness witness sharing one outer edge object. Neither
extensionality nor uniqueness of pair representatives is assumed. This is a
pointwise ingredient, not a clean-graph endpoint theorem, row construction,
multiplication totality, or a PA proof translation. -/
namespace PASoundness.PAtoCompactProductCleanCoordinateAlias
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactKuratowskiInjectivity
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Two decompositions of the same outer pair and the corresponding inner
pair entail equality of the three displayed coordinates. All syntactic
labels are distinct for capture avoidance; their denoted objects may alias. -/
def clean_coordinates : KDerivation
    (imp (pairFormula 19 18 5).encode
      (imp (pairFormula 19 53 52).encode
        (imp (pairFormula 18 3 4).encode
          (imp (pairFormula 53 50 51).encode
            (both (both (equal 3 50) (equal 4 51)) (equal 5 52)))))) := by
  let F := pairFormula 53 50 51
  have htransport := (equalityReplace 53 18 F (by decide) (by decide)).1
  have hsyntax : replace 53 18 F = pairFormula 18 50 51 := by decide
  rw [hsyntax] at htransport
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula 53 50 51).encode,(pairFormula 18 3 4).encode,
    (pairFormula 19 53 52).encode,(pairFormula 19 18 5).encode]
  have houter1 : Context Γ (pairFormula 19 18 5).encode := .hypothesis (by simp [Γ])
  have houter2 : Context Γ (pairFormula 19 53 52).encode := .hypothesis (by simp [Γ])
  have hinner1 : Context Γ (pairFormula 18 3 4).encode := .hypothesis (by simp [Γ])
  have hinner2 : Context Γ (pairFormula 53 50 51).encode := .head _ _
  have houter : Context Γ (both (equal 18 53) (equal 5 52)) :=
    .mp houter2 (.mp houter1 (.closed (pair_coordinates 19 18 5 53 52 (by decide))))
  have hp : Context Γ (equal 53 18) := Context.eqSymm (Context.conjunctionLeft houter)
  have hinner2' : Context Γ (pairFormula 18 50 51).encode := .mp hinner2 (.mp hp (.closed htransport))
  have hinner : Context Γ (both (equal 3 50) (equal 4 51)) :=
    .mp hinner2' (.mp hinner1 (.closed (pair_coordinates 18 3 4 50 51 (by decide))))
  exact Context.conjunctionIntro hinner (Context.conjunctionRight houter)

theorem clean_coordinates_certificate : theoremCode (certificate clean_coordinates) =
    imp (pairFormula 19 18 5).encode
      (imp (pairFormula 19 53 52).encode
        (imp (pairFormula 18 3 4).encode
          (imp (pairFormula 53 50 51).encode
            (both (both (equal 3 50) (equal 4 51)) (equal 5 52))))) :=
  certificate_correct clean_coordinates
end PASoundness.PAtoCompactProductCleanCoordinateAlias
#print axioms PASoundness.PAtoCompactProductCleanCoordinateAlias.clean_coordinates
#print axioms PASoundness.PAtoCompactProductCleanCoordinateAlias.clean_coordinates_certificate
