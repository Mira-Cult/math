import PASoundness.PAtoCompactSegmentBackwardContain
import PASoundness.PAtoCompactRestrictionEdgeEquivalence

/-! An original graph edge into an initial segment has its source endpoint in
the matching initial segment and survives a supplied endpoint filter. This is
pointwise: original totality, the filter witness and the full restricted
isomorphism remain separate obligations. Code 1 is literal self-membership. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentBackwardPoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactRestrictionEdgeEquivalence
open PASoundness.PAtoCompactSegmentBackwardContain
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def restriction : Nat := filterGraph 6 8 14 (edgePredicate 14 2 5).encode
def topEdge : Nat := (graphFormula 6 2 5).encode
def oldEdge : Nat := (graphFormula 6 7 3).encode
def restrictedEdge : Nat := (graphFormula 8 7 3).encode

/-- The displayed old edge is retained and its source is below the chosen
source endpoint. The target outer transitivity and domain guards are explicit. -/
def backward_point : KDerivation
    (imp (transitiveCode 1 16 18) (imp (member 1 5) (imp (member 0 2)
      (imp orderFormula.encode (imp restriction (imp topEdge
        (imp (member 0 7) (imp (member 5 3) (imp oldEdge
          (both (member 2 7) restrictedEdge)))))))))) := by
  let T := transitiveCode 1 16 18
  let V := member 1 5
  let U := member 0 2
  let O := orderFormula.encode
  let F := restriction
  let H := topEdge
  let X := member 0 7
  let Y := member 5 3
  let E := oldEdge
  let P := member 2 7
  let G := restrictedEdge
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [E,Y,X,H,F,O,U,V,T]
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hv : Context Γ V := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have hy : Context Γ Y := .hypothesis (by simp [Γ])
  have he : Context Γ E := .head _ _
  have hp : Context Γ P := .mp ho (.mp he (.mp hh (.mp hx (.mp hy
    (.mp hv (.mp hu (.mp ht (.closed backward_contain))))))))
  have iff : Context Γ (both (imp E G) (imp G E)) :=
    .mp hy (.mp hp (.mp hf (.closed (restricted_edge_iff 6 8 14 2 5 7 3 (by decide)))))
  exact Context.conjunctionIntro hp (.mp he (Context.conjunctionLeft iff))

theorem backward_point_certificate : theoremCode (certificate backward_point) =
    imp (transitiveCode 1 16 18) (imp (member 1 5) (imp (member 0 2)
      (imp orderFormula.encode (imp restriction (imp topEdge
        (imp (member 0 7) (imp (member 5 3) (imp oldEdge
          (both (member 2 7) restrictedEdge))))))))) :=
  certificate_correct backward_point

end PASoundness.PAtoCompactSegmentBackwardPoint

#print axioms PASoundness.PAtoCompactSegmentBackwardPoint.backward_point
#print axioms PASoundness.PAtoCompactSegmentBackwardPoint.backward_point_certificate
