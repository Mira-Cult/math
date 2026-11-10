import PASoundness.PAtoCompactSegmentBackwardGuard
import PASoundness.PAtoCompactBijectionBackwardAtThree

/-! Transfer a fixed original preimage's uniqueness to an endpoint-restricted
graph when the inner source is an element of a transitive outer source. The
outer transitivity, inner-source membership, filter, and original witness are
explicit K antecedents. This proves no coverage or quotient law. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentBackwardUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactSegmentBackwardGuard PASoundness.PAtoCompactBijectionBackwardAtThree
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Under the exact displayed hypotheses, the old preimage witness remains
unique among edges guarded by the inner source of the filtered graph. -/
def backward_unique : KDerivation
    (imp (transitiveCode 0 11 12) (imp (member 0 2)
      (imp (filterGraph 6 8 14 (edgePredicate 14 2 5).encode)
        (imp (witness 7).encode
          (allCode 4 (imp (both (member 2 4) (graphFormula 8 4 3).encode)
            (equal 4 7))))))) := by
  let T := transitiveCode 0 11 12
  let M := member 0 2
  let F := filterGraph 6 8 14 (edgePredicate 14 2 5).encode
  let W := (witness 7).encode
  let A := both (member 2 4) (graphFormula 8 4 3).encode
  let B := both (member 0 4) (graphFormula 6 4 3).encode
  let E := equal 4 7
  let Γ := [W,F,M,T]
  have hcompose : KDerivation (imp (imp A B) (imp (imp B E) (imp A E))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Δ := [A,imp B E,imp A B]
    have ha : Context Δ A := .head _ _
    have hab : Context Δ (imp A B) := .hypothesis (by simp [Δ])
    have hbe : Context Δ (imp B E) := .hypothesis (by simp [Δ])
    exact .mp (.mp ha hab) hbe
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hw : Context Γ W := .head _ _
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hguard : Context Γ (allCode 4 (imp A B)) :=
    .mp hf (.mp hm (.mp ht (.closed segment_backward_guard)))
  have hold : Context Γ (allCode 4 (imp B E)) :=
    Context.conjunctionRight (Context.conjunctionRight hw)
  have hc : Context Γ (allCode 4 (imp (imp A B) (imp (imp B E) (imp A E)))) :=
    .closed (.generalize 4 hcompose)
  have hnext : Context Γ (allCode 4 (imp (imp B E) (imp A E))) := Context.allMP hguard hc
  exact Context.allMP hold hnext

theorem backward_unique_certificate : theoremCode (certificate backward_unique) =
    imp (transitiveCode 0 11 12) (imp (member 0 2)
      (imp (filterGraph 6 8 14 (edgePredicate 14 2 5).encode)
        (imp (witness 7).encode
          (allCode 4 (imp (both (member 2 4) (graphFormula 8 4 3).encode)
            (equal 4 7)))))) :=
  certificate_correct backward_unique

end PASoundness.PAtoCompactSegmentBackwardUnique

#print axioms PASoundness.PAtoCompactSegmentBackwardUnique.backward_unique
#print axioms PASoundness.PAtoCompactSegmentBackwardUnique.backward_unique_certificate
