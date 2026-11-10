import PASoundness.PAtoCompactRestrictedBackwardGuard
import PASoundness.PAtoCompactBijectionBackwardAtThree

/-! Transfer the uniqueness clause of a supplied backward-bijection witness
to the endpoint-restricted graph. This is a local K derivation; it does not
establish witness existence or a full bijection. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedBackwardUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactRestrictedBackwardGuard PASoundness.PAtoCompactBijectionBackwardAtThree
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A supplied original preimage witness at 7 remains unique among guarded
edges of the restricted graph. The original witness's literal ∀4 uniqueness
clause and the separately derived guard transfer are combined by K universal
distribution; no bound variable in that witness is treated as syntactically
absent. Fixed names may denote the same object. -/
def backward_unique : KDerivation
    (imp (successorCode 2 0 9)
      (imp (filterGraph 6 8 14 (edgePredicate 14 2 5).encode)
        (imp (witness 7).encode
          (allCode 4 (imp (both (member 2 4) (graphFormula 8 4 3).encode)
            (equal 4 7)))))) := by
  let S := successorCode 2 0 9
  let F := filterGraph 6 8 14 (edgePredicate 14 2 5).encode
  let W := (witness 7).encode
  let A := both (member 2 4) (graphFormula 8 4 3).encode
  let B := both (member 0 4) (graphFormula 6 4 3).encode
  let E := equal 4 7
  let Γ := [W,F,S]
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
  have hw : Context Γ W := .head _ _
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hguard : Context Γ (allCode 4 (imp A B)) :=
    .mp hf (.mp hs (.closed backward_guard))
  have hold : Context Γ (allCode 4 (imp B E)) :=
    Context.conjunctionRight (Context.conjunctionRight hw)
  have hc : Context Γ (allCode 4 (imp (imp A B) (imp (imp B E) (imp A E)))) :=
    .closed (.generalize 4 hcompose)
  have hnext : Context Γ (allCode 4 (imp (imp B E) (imp A E))) := Context.allMP hguard hc
  exact Context.allMP hold hnext

theorem backward_unique_certificate : theoremCode (certificate backward_unique) =
    imp (successorCode 2 0 9)
      (imp (filterGraph 6 8 14 (edgePredicate 14 2 5).encode)
        (imp (witness 7).encode
          (allCode 4 (imp (both (member 2 4) (graphFormula 8 4 3).encode)
            (equal 4 7))))) :=
  certificate_correct backward_unique

end PASoundness.PAtoCompactRestrictedBackwardUnique

#print axioms PASoundness.PAtoCompactRestrictedBackwardUnique.backward_unique
#print axioms PASoundness.PAtoCompactRestrictedBackwardUnique.backward_unique_certificate
