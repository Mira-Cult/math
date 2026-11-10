import PASoundness.PAtoCompactPartialCompositionGuardedCaseJoin
import PASoundness.PAtoCompactQuantifiedRefutation

/-! Strong global induction step for the partial-composition predicate,
retaining both exact input-bijection formulas as object-level assumptions.
The inside-source proof remains supplied proof data; graph collection and
candidate induction are not established here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionGuardedGlobalStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityEdgeForward
open PASoundness.PAtoCompactPartialCompositionPredicate PASoundness.PAtoCompactPartialCompositionGuardedCaseJoin
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Both input graphs' literal bijection formulas and a supplied inside-source
step yield the exact strong candidate-induction schema. Source 0, middle 1,
target 8, and input graphs 6 and 7 remain free parameters. -/
def guarded_global_step_of_inside
    (inside : KDerivation (imp bijectionFormula.encode (imp secondBijection.encode
      (imp (successorCode 10 13 15) (imp (member 0 10)
        (imp (replace 30 10 predicate).encode (replace 30 13 predicate).encode)))))) :
    KDerivation (imp bijectionFormula.encode (imp secondBijection.encode
      (allCode 31 (allStepsCode 31 30 10 13 15 32 33 predicate)))) := by
  let B₁ := bijectionFormula.encode
  let B₂ := secondBijection.encode
  let P := (replace 30 10 predicate).encode
  let Q := (replace 30 13 predicate).encode
  let S := successorCode 10 13 15
  let C := predecessorCore 31 10 13 15 32 33
  let Γ := [B₂,B₁]
  have hb₁ : Context Γ B₁ := .hypothesis (by simp [Γ])
  have hb₂ : Context Γ B₂ := Context.head _ _
  have hs : Context Γ (imp S (imp P Q)) :=
    .mp hb₂ (.mp hb₁ (.closed (guarded_successor_of_inside inside)))
  have hp : Context Γ (imp C (imp P Q)) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := [P,C,B₂,B₁]
    have hP : Context Δ P := Context.head _ _
    have hC : Context Δ C := .hypothesis (by simp [Δ])
    have hS : Context Δ S := Context.conjunctionLeft (Context.conjunctionRight hC)
    exact .mp hP (.mp hS (Context.under (Context.under hs C) P))
  have hv (v : Nat) (fresh₁ : v ∉ bijectionFormula.names)
      (fresh₂ : v ∉ secondBijection.names) :
      ∀ q, q ∈ Γ → KDerivation (imp q (allCode v q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases h : q = B₂
    · subst q
      exact secondBijection.vacuity v fresh₂
    · have h' : q = B₁ := hq.resolve_left h
      subst q
      exact bijectionFormula.vacuity v fresh₁
  have hall := Context.generalize 31 (hv 31 (by decide) (by decide))
    (Context.generalize 13 (hv 13 (by decide) (by decide))
      (Context.generalize 10 (hv 10 (by decide) (by decide)) hp))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hall

theorem guarded_global_step_of_inside_certificate
    (inside : KDerivation (imp bijectionFormula.encode (imp secondBijection.encode
      (imp (successorCode 10 13 15) (imp (member 0 10)
        (imp (replace 30 10 predicate).encode (replace 30 13 predicate).encode)))))) :
    theoremCode (certificate (guarded_global_step_of_inside inside)) =
      imp bijectionFormula.encode (imp secondBijection.encode
        (allCode 31 (allStepsCode 31 30 10 13 15 32 33 predicate))) :=
  certificate_correct (guarded_global_step_of_inside inside)

end PASoundness.PAtoCompactPartialCompositionGuardedGlobalStep

#print axioms PASoundness.PAtoCompactPartialCompositionGuardedGlobalStep.guarded_global_step_of_inside
#print axioms PASoundness.PAtoCompactPartialCompositionGuardedGlobalStep.guarded_global_step_of_inside_certificate
