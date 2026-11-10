import PASoundness.PAtoCompactProductOutputTripleEdgeSplit
import PASoundness.PAtoCompactKuratowskiInjectivity

/-! Refine the new-edge branch of the single-triple adjunction using the
explicit inner pair descriptions. Pair representatives need not be unique;
the K pair-injectivity proof compares their coordinates. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputTripleCoordinateSplit

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactKuratowskiInjectivity
open PASoundness.PAtoCompactProductOutputTripleEdgeSplit

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Equal inner pair representatives imply equality of the queried and
selected coordinates, in queried-to-selected orientation. -/
def inner_pair_coordinates : KDerivation (imp (equal 55 11)
    (imp (pairFormula 11 30 31).encode (imp (pairFormula 55 56 57).encode
      (both (equal 56 30) (equal 57 31))))) := by
  have ht := (equalityReplace 55 11 (pairFormula 55 56 57) (by decide) (by decide)).1
  have hs : replace 55 11 (pairFormula 55 56 57) = pairFormula 11 56 57 := by decide
  rw [hs] at ht
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula 55 56 57).encode,(pairFormula 11 30 31).encode,equal 55 11]
  have hquery : Context Γ (pairFormula 55 56 57).encode := .head _ _
  have hselected : Context Γ (pairFormula 11 30 31).encode := .hypothesis (by simp [Γ])
  have heq : Context Γ (equal 55 11) := .hypothesis (by simp [Γ])
  have hsame : Context Γ (pairFormula 11 56 57).encode := .mp hquery (.mp heq (.closed ht))
  have hc : Context Γ (both (equal 30 56) (equal 31 57)) :=
    .mp hsame (.mp hselected (.closed (pair_coordinates 11 30 31 56 57 (by decide))))
  exact Context.conjunctionIntro (Context.eqSymm (Context.conjunctionLeft hc))
    (Context.eqSymm (Context.conjunctionRight hc))

/-- Each queried new edge is old or has the selected factor coordinates and
selected image output. All three pair/edge witnesses remain explicit. -/
def triple_coordinate_split : KDerivation (imp (adjoinCode 58 12 9 16)
    (imp (pairFormula 12 11 33).encode (imp (pairFormula 11 30 31).encode
      (imp (pairFormula 55 56 57).encode (imp (graphFormula 9 55 60).encode
        (either (graphFormula 58 55 60).encode
          (both (equal 56 30) (both (equal 57 31) (equal 60 33))))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 9 55 60).encode,(pairFormula 55 56 57).encode,
    (pairFormula 11 30 31).encode,(pairFormula 12 11 33).encode,adjoinCode 58 12 9 16]
  have hg : Context Γ (graphFormula 9 55 60).encode := .head _ _
  have hq : Context Γ (pairFormula 55 56 57).encode := .hypothesis (by simp [Γ])
  have hc : Context Γ (pairFormula 11 30 31).encode := .hypothesis (by simp [Γ])
  have hp : Context Γ (pairFormula 12 11 33).encode := .hypothesis (by simp [Γ])
  have ha : Context Γ (adjoinCode 58 12 9 16) := .hypothesis (by simp [Γ])
  have hs := Context.mp hg (Context.mp hp (Context.mp ha (.closed triple_edge_split)))
  apply Context.disjunctionElim hs
  · exact Context.disjunctionLeft (.head _ _)
  · let Δ := both (equal 55 11) (equal 60 33) :: Γ
    have he : Context Δ (both (equal 55 11) (equal 60 33)) := .head _ _
    have hi := Context.mp (.under hq _) (Context.mp (.under hc _)
      (Context.mp (Context.conjunctionLeft he) (.closed inner_pair_coordinates)))
    have ho : Context Δ (both (equal 56 30) (both (equal 57 31) (equal 60 33))) :=
      Context.conjunctionIntro (Context.conjunctionLeft hi)
        (Context.conjunctionIntro (Context.conjunctionRight hi) (Context.conjunctionRight he))
    exact Context.disjunctionRight ho

theorem triple_coordinate_split_certificate : theoremCode (certificate triple_coordinate_split) =
    imp (adjoinCode 58 12 9 16) (imp (pairFormula 12 11 33).encode
      (imp (pairFormula 11 30 31).encode (imp (pairFormula 55 56 57).encode
        (imp (graphFormula 9 55 60).encode (either (graphFormula 58 55 60).encode
          (both (equal 56 30) (both (equal 57 31) (equal 60 33)))))))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputTripleCoordinateSplit

#print axioms PASoundness.PAtoCompactProductOutputTripleCoordinateSplit.inner_pair_coordinates
#print axioms PASoundness.PAtoCompactProductOutputTripleCoordinateSplit.triple_coordinate_split
#print axioms PASoundness.PAtoCompactProductOutputTripleCoordinateSplit.triple_coordinate_split_certificate
