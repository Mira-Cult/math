import PASoundness.PAtoCompactRestrictedBackwardWitness

/-! Backward witness transfer over arbitrary transitive outer domains. The
pointwise edge and uniqueness transfers remain explicit K proof-data inputs. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentBackwardAssembly
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactRestrictedBackwardPoint PASoundness.PAtoCompactRestrictionFilterVacuity
open PASoundness.PAtoCompactBijectionBackwardAtThree PASoundness.PAtoCompactRestrictedBackwardWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceTrans : Nat := transitiveCode 0 11 12
def targetTrans : Nat := transitiveCode 1 16 18
def pointGoal : Nat := imp targetTrans (imp (member 1 5) (imp (member 0 2)
  (imp orderFormula.encode (imp restriction (imp topEdge
    (imp (member 0 7) (imp (member 5 3) (imp oldEdge
      (both (member 2 7) restrictedEdge)))))))))
def uniqueGoal : Nat := imp sourceTrans (imp (member 0 2) (imp restriction
  (imp (witness 7).encode (allCode 4
    (imp (both (member 2 4) (graphFormula 8 4 3).encode) (equal 4 7))))))
def fullGoal : Nat := imp sourceTrans (imp targetTrans (imp (member 0 2) (imp (member 1 5)
  (imp orderFormula.encode (imp bijectionFormula.encode (imp restriction (imp topEdge
    (imp (member 5 3) (existsCode 7 restrictedWitness.encode)))))))))

/-- Assemble a restricted preimage witness from explicitly supplied K point
and uniqueness derivations. -/
def backward_witness_of_point_unique
    (point : KDerivation pointGoal) (unique : KDerivation uniqueGoal) :
    KDerivation fullGoal := by
  let X := sourceTrans
  let Y := targetTrans
  let A := member 0 2
  let D := member 1 5
  let O := orderFormula.encode
  let B := bijectionFormula.encode
  let F := restriction
  let T := topEdge
  let V := member 5 3
  let W := (witness 7).encode
  let R := restrictedWitness.encode
  let Γ := [V,T,F,B,O,D,A,Y,X]
  have hctx : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 7 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases he : z = V
    · subst z; exact membershipVacuity 5 3 7 (by decide) (by decide)
    by_cases he : z = T
    · subst z; exact (graphFormula 6 2 5).vacuity 7 (by decide)
    by_cases he : z = F
    · subst z; exact restriction_filter_vacuity 6 8 14 2 5 7 (by decide)
    by_cases he : z = B
    · subst z; exact bijectionFormula.vacuity 7 (by decide)
    by_cases he : z = O
    · subst z; exact orderFormula.vacuity 7 (by decide)
    by_cases he : z = D
    · subst z; exact membershipVacuity 1 5 7 (by decide) (by decide)
    by_cases he : z = A
    · subst z; exact membershipVacuity 0 2 7 (by decide) (by decide)
    by_cases he : z = Y
    · subst z; exact transitive_vacuity 1 16 18 7 (by decide) (by decide) (by decide)
    have he : z = X := by simp_all
    subst z
    exact transitive_vacuity 0 11 12 7 (by decide) (by decide) (by decide)

  have hlocal : Context Γ (imp W R) := by
    apply Context.deduction
    let Δ := W :: Γ
    have hw : Context Δ W := .head _ _
    have hu : Context Δ (member 0 7) := Context.conjunctionLeft hw
    have he : Context Δ oldEdge := Context.conjunctionLeft (Context.conjunctionRight hw)
    have hx : Context Δ X := .hypothesis (by simp [Δ,Γ])
    have hy : Context Δ Y := .hypothesis (by simp [Δ,Γ])
    have ha : Context Δ A := .hypothesis (by simp [Δ,Γ])
    have hd : Context Δ D := .hypothesis (by simp [Δ,Γ])
    have ho : Context Δ O := .hypothesis (by simp [Δ,Γ])
    have hf : Context Δ F := .hypothesis (by simp [Δ,Γ])
    have ht : Context Δ T := .hypothesis (by simp [Δ,Γ])
    have hv : Context Δ V := .hypothesis (by simp [Δ,Γ])
    have hpoint : Context Δ (both (member 2 7) restrictedEdge) := by
      have hp : Context Δ pointGoal := .closed point
      exact .mp he (.mp hv (.mp hu (.mp ht (.mp hf (.mp ho (.mp ha (.mp hd (.mp hy hp))))))))
    have huniq : Context Δ (allCode 4
        (imp (both (member 2 4) (graphFormula 8 4 3).encode) (equal 4 7))) := by
      have hp : Context Δ uniqueGoal := .closed unique
      exact .mp hw (.mp hf (.mp ha (.mp hx hp)))
    exact Context.conjunctionIntro (Context.conjunctionLeft hpoint)
      (Context.conjunctionIntro (Context.conjunctionRight hpoint) huniq)
  have horiginal : Context Γ (existsCode 7 W) := by
    have hv : Context Γ V := .hypothesis (by simp [Γ])
    have hy : Context Γ Y := .hypothesis (by simp [Γ])
    have hd : Context Γ D := .hypothesis (by simp [Γ])
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have hmember : Context Γ (member 1 3) :=
      .mp hv (.mp hd (.mp hy (.closed (transitive_chain 1 16 18 5 3
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))))
    exact .mp hmember (.mp hb (.closed backward_witness))
  have hresult : Context Γ (existsCode 7 R) :=
    exists_map_context (Context.generalize 7 hctx hlocal) horiginal
  change KDerivation (imp X (imp Y (imp A (imp D (imp O (imp B (imp F (imp T (imp V (existsCode 7 R))))))))))
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
  exact hresult

theorem backward_witness_of_point_unique_certificate
    (point : KDerivation pointGoal) (unique : KDerivation uniqueGoal) :
    theoremCode (certificate (backward_witness_of_point_unique point unique)) = fullGoal :=
  certificate_correct (backward_witness_of_point_unique point unique)

end PASoundness.PAtoCompactSegmentBackwardAssembly

#print axioms PASoundness.PAtoCompactSegmentBackwardAssembly.backward_witness_of_point_unique
#print axioms PASoundness.PAtoCompactSegmentBackwardAssembly.backward_witness_of_point_unique_certificate
