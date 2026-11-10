import PASoundness.PAtoCompactMaximumPreimage
import PASoundness.PAtoCompactMaximumAlignment
import PASoundness.PAtoCompactMaximumGraphFunctionClosed
import PASoundness.PAtoCompactMaximumOrderAligned

/-! A guarded K maximum-image step for a supplied represented graph.
It does not construct the graph, edges or preimage and does not establish
quotient equivalence or successor cancellation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMaximumImagePoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactMaximumPreimage
open PASoundness.PAtoCompactMaximumAlignment
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Names 2 and 5 are old maxima, 0 and 1 their supplied successors, 6 the
supplied graph, 3 the image of 2 and 7 a preimage of 5. Under both exact
bijection/order clauses, both successor graphs, transitivity of 5, all
displayed source/target guards and both edges, K derives `3=5`. The named
labels are syntactically distinct; their assigned objects may coincide.
Negation in imported proofs is literal implication to code 1. -/
def maximum_image_point : KDerivation
    (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (transitiveCode 5 11 12) (imp bijectionFormula.encode
        (imp orderFormula.encode (imp (member 0 7) (imp (member 0 2)
          (imp (member 1 5) (imp (member 1 3)
            (imp (graphFormula 6 7 5).encode (imp (graphFormula 6 2 3).encode
              (equal 3 5)))))))))))) := by
  let SX := successorCode 2 0 9
  let SY := successorCode 5 1 10
  let T := transitiveCode 5 11 12
  let B := bijectionFormula.encode
  let O := orderFormula.encode
  let A := member 0 7
  let X := member 0 2
  let Y := member 1 5
  let Z := member 1 3
  let G := (graphFormula 6 7 5).encode
  let H := (graphFormula 6 2 3).encode
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
  apply Context.deduction
  apply Context.deduction
  let Γ := [H,G,Z,Y,X,A,O,B,T,SY,SX]
  have hsx : Context Γ SX := .hypothesis (by simp [Γ])
  have hsy : Context Γ SY := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have hy : Context Γ Y := .hypothesis (by simp [Γ])
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hh : Context Γ H := .head _ _
  have hfunction : Context Γ (imp (equal 7 2) (equal 3 5)) :=
    .mp hg (.mp hy (.mp hh (.mp hz (.mp hx (.mp hb
      (.closed PAtoCompactMaximumGraphFunctionClosed.equal_inputs_force_equal_images))))))
  have horder : Context Γ (imp (member 2 7) (member 3 5)) :=
    .mp hh (.mp hg (.mp hz (.mp hy (.mp hx (.mp ha (.mp ho
      (.closed PAtoCompactMaximumOrderAligned.proper_preimage_order)))))))
  have hproper : Context Γ (imp (neg (equal 3 5)) (member 3 5)) :=
    .mp horder (.mp hfunction (.mp ha (.mp hsx
      (.closed (proper_image_from_preimage 2 0 7 9 3 5 (by decide) (by decide) (by decide))))))
  exact .mp hproper (.mp hz (.mp ht (.mp hsy
    (.closed (maximum_alignment 5 1 3 10 11 12 (by decide))))))

theorem maximum_image_point_certificate :
    theoremCode (certificate maximum_image_point) =
      imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
        (imp (transitiveCode 5 11 12) (imp bijectionFormula.encode
          (imp orderFormula.encode (imp (member 0 7) (imp (member 0 2)
            (imp (member 1 5) (imp (member 1 3)
              (imp (graphFormula 6 7 5).encode (imp (graphFormula 6 2 3).encode
                (equal 3 5))))))))))) :=
  certificate_correct maximum_image_point

end PASoundness.PAtoCompactMaximumImagePoint

#print axioms PASoundness.PAtoCompactMaximumImagePoint.maximum_image_point
#print axioms PASoundness.PAtoCompactMaximumImagePoint.maximum_image_point_certificate
