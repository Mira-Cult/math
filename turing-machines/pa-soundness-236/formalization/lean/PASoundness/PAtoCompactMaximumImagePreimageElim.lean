import PASoundness.PAtoCompactMaximumImagePoint
import PASoundness.PAtoCompactBijectionBackwardPreimage

/-! Eliminate the exposed preimage from the guarded K maximum-image step.
The source and target successor graphs, exact isomorphism clauses, and the
chosen image edge remain explicit premises. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMaximumImagePreimageElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactMaximumImagePoint
open PASoundness.PAtoCompactBijectionBackwardPreimage
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def target : Formula :=
  .imp (.all 9 (namedSuccessorBody 2 0 9))
    (.imp (.all 10 (namedSuccessorBody 5 1 10))
      (.imp (.all 11 (.all 12 (transitiveBody 5 11 12)))
        (.imp bijectionFormula (.imp orderFormula
          (.imp (.member 0 2) (.imp (.member 1 5) (.imp (.member 1 3)
            (.imp (graphFormula 6 2 3) (.equal 3 5)))))))))

/-- Given the two raw successor graphs, transitivity of the target's old
maximum, the exact bijection and order clauses, source guard 2∈0, target
guards 5∈1 and 3∈1, and the edge 2→3, K derives 3=5. The needed preimage
of 5 is obtained from the supplied bijection and eliminated using the
literal vacuity rule at fresh name 7. No graph is constructed. -/
def maximum_image_of_edge : KDerivation
    (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (transitiveCode 5 11 12) (imp bijectionFormula.encode
        (imp orderFormula.encode (imp (member 0 2)
          (imp (member 1 5) (imp (member 1 3)
            (imp (graphFormula 6 2 3).encode (equal 3 5)))))))))) := by
  let W := (witnessBody 7 5).encode
  have hv : KDerivation (imp target.encode (allCode 7 target.encode)) :=
    target.vacuity 7 (by decide)
  have hlocal : KDerivation (imp W target.encode) := by
    change KDerivation (imp W (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (transitiveCode 5 11 12) (imp bijectionFormula.encode
        (imp orderFormula.encode (imp (member 0 2)
          (imp (member 1 5) (imp (member 1 3)
            (imp (graphFormula 6 2 3).encode (equal 3 5)))))))))))
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
    let SX := successorCode 2 0 9
    let SY := successorCode 5 1 10
    let T := transitiveCode 5 11 12
    let B := bijectionFormula.encode
    let O := orderFormula.encode
    let X := member 0 2
    let Y := member 1 5
    let Z := member 1 3
    let H := (graphFormula 6 2 3).encode
    let Γ := [H,Z,Y,X,O,B,T,SY,SX,W]
    have hsx : Context Γ SX := .hypothesis (by simp [Γ])
    have hsy : Context Γ SY := .hypothesis (by simp [Γ])
    have ht : Context Γ T := .hypothesis (by simp [Γ])
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have ho : Context Γ O := .hypothesis (by simp [Γ])
    have hx : Context Γ X := .hypothesis (by simp [Γ])
    have hy : Context Γ Y := .hypothesis (by simp [Γ])
    have hz : Context Γ Z := .hypothesis (by simp [Γ])
    have hh : Context Γ H := .head _ _
    have hw : Context Γ W := .hypothesis (by simp [Γ])
    have ha : Context Γ (member 0 7) := Context.conjunctionLeft hw
    have hg : Context Γ (graphFormula 6 7 5).encode :=
      Context.conjunctionLeft (Context.conjunctionRight hw)
    exact .mp hh (.mp hg (.mp hz (.mp hy (.mp hx (.mp ha (.mp ho
      (.mp hb (.mp ht (.mp hsy (.mp hsx (.closed maximum_image_point)))))))))))
  have helim : KDerivation (imp (existsCode 7 W) target.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv (.closed (.generalize 7 hlocal))
      (Context.head [] (existsCode 7 W))
  change KDerivation target.encode
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
  let Γ := [(graphFormula 6 2 3).encode, member 1 3, member 1 5, member 0 2,
    orderFormula.encode, bijectionFormula.encode, transitiveCode 5 11 12,
    successorCode 5 1 10, successorCode 2 0 9]
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hy : Context Γ (member 1 5) := .hypothesis (by simp [Γ])
  have hw : Context Γ (existsCode 7 W) := .mp hy (.mp hb (.closed backward_preimage))
  have ht : Context Γ target.encode := .mp hw (.closed helim)
  exact .mp (Context.head _ _) (.mp (.hypothesis (by simp))
    (.mp hy (.mp (.hypothesis (by simp)) (.mp (.hypothesis (by simp))
      (.mp hb (.mp (.hypothesis (by simp)) (.mp (.hypothesis (by simp))
        (.mp (.hypothesis (by simp)) ht))))))))

theorem maximum_image_of_edge_certificate :
    theoremCode (certificate maximum_image_of_edge) =
      imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
        (imp (transitiveCode 5 11 12) (imp bijectionFormula.encode
          (imp orderFormula.encode (imp (member 0 2)
            (imp (member 1 5) (imp (member 1 3)
              (imp (graphFormula 6 2 3).encode (equal 3 5))))))))) :=
  certificate_correct maximum_image_of_edge

end PASoundness.PAtoCompactMaximumImagePreimageElim

#print axioms PASoundness.PAtoCompactMaximumImagePreimageElim.maximum_image_of_edge
#print axioms PASoundness.PAtoCompactMaximumImagePreimageElim.maximum_image_of_edge_certificate
