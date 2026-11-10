import PASoundness.PAtoCompactCommonSourceSpanFixtureNames
import PASoundness.PAtoCompactQuantifiedRefutation

/-! Strong candidate-induction successor schema for common-source span graphs.
The two literal forward-bijection clauses remain K antecedents; no candidate
induction or complete span graph is asserted in this module. -/
namespace PASoundness.PAtoCompactCommonSourceSpanGlobalStep

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCommonSourceSpanImages PASoundness.PAtoCompactCommonSourceSpanSuccessor

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The fixed step yields the exact strong-step schema. Both source graph
clauses remain object-level inputs, and no image candidate is assumed. -/
def global_step : KDerivation (imp firstClause.encode (imp secondClause.encode
    (allCode 31 (allStepsCode 31 30 10 13 15 32 33 inductionPredicate)))) := by
  let B₁ := firstClause.encode
  let B₂ := secondClause.encode
  let P := (replace 30 10 inductionPredicate).encode
  let Q := (replace 30 13 inductionPredicate).encode
  let S := successorCode 10 13 15
  let C := predecessorCore 31 10 13 15 32 33
  let Γ := [B₂,B₁]
  have hb₁ : Context Γ B₁ := .hypothesis (by simp [Γ])
  have hb₂ : Context Γ B₂ := .head _ _
  have hs : Context Γ (imp S (imp P Q)) := by
    apply Context.deduction
    let Δ := [S,B₂,B₁]
    have hS : Context Δ S := .head _ _
    have hguard : Context Δ fixedGuard.encode := Context.conjunctionIntro (.under hb₁ _)
      (Context.conjunctionIntro (.under hb₂ _) hS)
    exact .mp hguard (.closed induction_successor)
  have hp : Context Γ (imp C (imp P Q)) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := [P,C,B₂,B₁]
    have hP : Context Δ P := .head _ _
    have hC : Context Δ C := .hypothesis (by simp [Δ])
    have hS : Context Δ S := Context.conjunctionLeft (Context.conjunctionRight hC)
    exact .mp hP (.mp hS (.under (.under hs C) P))
  have hv (v : Nat) (fresh₁ : v ∉ firstClause.names)
      (fresh₂ : v ∉ secondClause.names) :
      ∀ q, q ∈ Γ → KDerivation (imp q (allCode v q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = B₂
    · subst q; exact secondClause.vacuity v fresh₂
    · have he' : q = B₁ := hq.resolve_left he
      subst q; exact firstClause.vacuity v fresh₁
  have hall := Context.generalize 31 (hv 31 (by decide) (by decide))
    (Context.generalize 13 (hv 13 (by decide) (by decide))
      (Context.generalize 10 (hv 10 (by decide) (by decide)) hp))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hall

theorem global_step_certificate : theoremCode (certificate global_step) =
    imp firstClause.encode (imp secondClause.encode
      (allCode 31 (allStepsCode 31 30 10 13 15 32 33 inductionPredicate))) :=
  certificate_correct global_step

end PASoundness.PAtoCompactCommonSourceSpanGlobalStep

#print axioms PASoundness.PAtoCompactCommonSourceSpanGlobalStep.global_step
#print axioms PASoundness.PAtoCompactCommonSourceSpanGlobalStep.global_step_certificate
