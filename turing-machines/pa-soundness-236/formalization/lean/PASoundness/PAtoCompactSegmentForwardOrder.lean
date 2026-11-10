import PASoundness.PAtoCompactSegmentOrderPoint
import PASoundness.PAtoCompactTransitiveClosure

/-! A supplied order-isomorphism edge sends an element of an initial segment
into the corresponding target initial segment. This is literal K proof data
with every domain and graph guard explicit; it does not construct either
edge, a restricted graph, or a quotient interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentForwardOrder
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSegmentOrderPoint
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Outer source 0 is transitive, 2∈0, 7∈2, 3 and 5∈1, and supplied graph
edges are 7→3 and 2→5. The displayed order clause then gives 3∈5. -/
def forward_segment_order : KDerivation
    (imp (transitiveCode 0 11 12) (imp (member 0 2) (imp (member 2 7)
      (imp (member 1 3) (imp (member 1 5)
        (imp (graphFormula 6 7 3).encode (imp (graphFormula 6 2 5).encode
          (imp orderFormula.encode (member 5 3))))))))) := by
  let T := transitiveCode 0 11 12
  let U := member 0 2
  let I := member 2 7
  let J := member 1 3
  let V := member 1 5
  let E := (graphFormula 6 7 3).encode
  let F := (graphFormula 6 2 5).encode
  let O := orderFormula.encode
  let Γ := [O,F,E,V,J,I,U,T]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hi : Context Γ I := .hypothesis (by simp [Γ])
  have hj : Context Γ J := .hypothesis (by simp [Γ])
  have hv : Context Γ V := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .head _ _
  have hsrc : Context Γ (member 0 7) := .mp hi (.mp hu (.mp ht
    (.closed (transitive_chain 0 11 12 2 7 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)))))
  have hord : Context Γ (both (imp I (member 5 3)) (imp (member 5 3) I)) :=
    .mp hf (.mp he (.mp hv (.mp hj (.mp hu (.mp hsrc (.mp ho
      (.closed guarded_segment_order)))))))
  exact .mp hi (Context.conjunctionLeft hord)

theorem forward_segment_order_certificate : theoremCode (certificate forward_segment_order) =
    imp (transitiveCode 0 11 12) (imp (member 0 2) (imp (member 2 7)
      (imp (member 1 3) (imp (member 1 5)
        (imp (graphFormula 6 7 3).encode (imp (graphFormula 6 2 5).encode
          (imp orderFormula.encode (member 5 3)))))))) :=
  certificate_correct forward_segment_order

end PASoundness.PAtoCompactSegmentForwardOrder

#print axioms PASoundness.PAtoCompactSegmentForwardOrder.forward_segment_order
#print axioms PASoundness.PAtoCompactSegmentForwardOrder.forward_segment_order_certificate
