import PASoundness.PAtoCompactKuratowskiInjectivity
import PASoundness.CompactNamed

/-! Coordinate comparison for one queried product edge and one explicit
new-row witness sharing the same outer edge object. This constructs literal K
proofs without uniqueness of pair representatives, extensionality or semantic
soundness. It does not construct a row graph, establish graph membership, or
prove a multiplication theorem. -/
namespace PASoundness.PAtoCompactMultiplicationRowCoordinateAlias
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactKuratowskiInjectivity
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- If one outer edge object simultaneously represents the queried inner
pair/value and the fixed-row inner pair/value, the corresponding first,
second and output coordinates are equal. The labels 60–62 are fresh row
witness names; actual values may coincide. -/
def row_coordinates : KDerivation
    (imp (pairFormula 63 18 5).encode
      (imp (pairFormula 63 62 61).encode
        (imp (pairFormula 18 3 4).encode
          (imp (pairFormula 62 30 60).encode
            (both (both (equal 3 30) (equal 4 60)) (equal 5 61)))))) := by
  let F := pairFormula 62 30 60
  have htransport := (equalityReplace 62 18 F (by decide) (by decide)).1
  have hsyntax : replace 62 18 F = pairFormula 18 30 60 := by decide
  rw [hsyntax] at htransport
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula 62 30 60).encode,(pairFormula 18 3 4).encode,
    (pairFormula 63 62 61).encode,(pairFormula 63 18 5).encode]
  have houter1 : Context Γ (pairFormula 63 18 5).encode := .hypothesis (by simp [Γ])
  have houter2 : Context Γ (pairFormula 63 62 61).encode := .hypothesis (by simp [Γ])
  have hinner1 : Context Γ (pairFormula 18 3 4).encode := .hypothesis (by simp [Γ])
  have hinner2 : Context Γ (pairFormula 62 30 60).encode := .head _ _
  have houter : Context Γ (both (equal 18 62) (equal 5 61)) :=
    .mp houter2 (.mp houter1 (.closed (pair_coordinates 63 18 5 62 61 (by decide))))
  have hp : Context Γ (equal 62 18) := Context.eqSymm (Context.conjunctionLeft houter)
  have hinner2' : Context Γ (pairFormula 18 30 60).encode := .mp hinner2 (.mp hp (.closed htransport))
  have hinner : Context Γ (both (equal 3 30) (equal 4 60)) :=
    .mp hinner2' (.mp hinner1 (.closed (pair_coordinates 18 3 4 30 60 (by decide))))
  exact Context.conjunctionIntro hinner (Context.conjunctionRight houter)

theorem row_coordinates_certificate : theoremCode (certificate row_coordinates) =
    imp (pairFormula 63 18 5).encode
      (imp (pairFormula 63 62 61).encode
        (imp (pairFormula 18 3 4).encode
          (imp (pairFormula 62 30 60).encode
            (both (both (equal 3 30) (equal 4 60)) (equal 5 61))))) :=
  certificate_correct row_coordinates
end PASoundness.PAtoCompactMultiplicationRowCoordinateAlias
#print axioms PASoundness.PAtoCompactMultiplicationRowCoordinateAlias.row_coordinates
#print axioms PASoundness.PAtoCompactMultiplicationRowCoordinateAlias.row_coordinates_certificate
