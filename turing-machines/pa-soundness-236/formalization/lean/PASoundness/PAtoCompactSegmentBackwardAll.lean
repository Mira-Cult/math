import PASoundness.PAtoCompactSegmentBackwardAssembly
import PASoundness.PAtoCompactBijectionVacuity
import PASoundness.PAtoCompactOrderIsoVacuity

/-! Quantification of a supplied pointwise K derivation for backward
coverage by an initial-segment restriction. All outer transitivity, endpoint
membership, isomorphism, restriction and top-edge premises are retained.
The pointwise proof remains a metatheoretic proof-data argument. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentBackwardAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactRestrictedBackwardPoint PASoundness.PAtoCompactRestrictedBackwardWitness
open PASoundness.PAtoCompactSegmentBackwardAssembly
open PASoundness.PAtoCompactRestrictionFilterVacuity PASoundness.PAtoCompactBijectionVacuity
open PASoundness.PAtoCompactOrderIsoVacuity
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def allGoal : Nat := imp sourceTrans (imp targetTrans (imp (member 0 2) (imp (member 1 5)
  (imp orderFormula.encode (imp bijectionFormula.encode (imp restriction (imp topEdge
    (allCode 3 (imp (member 5 3) (existsCode 7 restrictedWitness.encode))))))))))

/-- A supplied pointwise backward-witness derivation yields the quantified
clause, preserving the same existential witness and its uniqueness condition. -/
def backward_all_of_point (point : KDerivation fullGoal) : KDerivation allGoal := by
  let X := sourceTrans
  let Y := targetTrans
  let A := member 0 2
  let D := member 1 5
  let O := orderFormula.encode
  let B := bijectionFormula.encode
  let F := restriction
  let T := topEdge
  let V := member 5 3
  let C := existsCode 7 restrictedWitness.encode
  let Γ := [T,F,B,O,D,A,Y,X]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 3 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases he : z = T
    · subst z; exact (graphFormula 6 2 5).vacuity 3 (by decide)
    by_cases he : z = F
    · subst z; exact restriction_filter_vacuity 6 8 14 2 5 3 (by decide)
    by_cases he : z = B
    · subst z; exact bijection_vacuity_three
    by_cases he : z = O
    · subst z; exact order_vacuity 3 order_fresh_3
    by_cases he : z = D
    · subst z; exact membershipVacuity 1 5 3 (by decide) (by decide)
    by_cases he : z = A
    · subst z; exact membershipVacuity 0 2 3 (by decide) (by decide)
    by_cases he : z = Y
    · subst z; exact transitive_vacuity 1 16 18 3 (by decide) (by decide) (by decide)
    have he : z = X := by simp_all
    subst z
    exact transitive_vacuity 0 11 12 3 (by decide) (by decide) (by decide)
  have hpoint : Context Γ (imp V C) := by
    have hx : Context Γ X := .hypothesis (by simp [Γ])
    have hy : Context Γ Y := .hypothesis (by simp [Γ])
    have ha : Context Γ A := .hypothesis (by simp [Γ])
    have hd : Context Γ D := .hypothesis (by simp [Γ])
    have ho : Context Γ O := .hypothesis (by simp [Γ])
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have hf : Context Γ F := .hypothesis (by simp [Γ])
    have ht : Context Γ T := .head _ _
    have hp : Context Γ fullGoal := .closed point
    exact .mp ht (.mp hf (.mp hb (.mp ho (.mp hd (.mp ha (.mp hy (.mp hx hp)))))))
  have hall : Context Γ (allCode 3 (imp V C)) := Context.generalize 3 hv hpoint
  change KDerivation (imp X (imp Y (imp A (imp D (imp O (imp B (imp F (imp T (allCode 3 (imp V C))))))))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hall

theorem backward_all_of_point_certificate (point : KDerivation fullGoal) :
    theoremCode (certificate (backward_all_of_point point)) = allGoal :=
  certificate_correct (backward_all_of_point point)

end PASoundness.PAtoCompactSegmentBackwardAll

#print axioms PASoundness.PAtoCompactSegmentBackwardAll.backward_all_of_point
#print axioms PASoundness.PAtoCompactSegmentBackwardAll.backward_all_of_point_certificate
