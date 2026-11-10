import PASoundness.PAtoCompactPartialInverseGuardedCaseJoin
import PASoundness.PAtoCompactQuantifiedRefutation

/-! Strong global step for the partial-inverse predicate, retaining the exact
forward-bijection formula as an object-level assumption throughout. The
inside-source proof remains a supplied derivation; inverse existence and
candidate induction are not asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseGuardedGlobalStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPartialInversePredicate PASoundness.PAtoCompactPartialInverseGuardedCaseJoin
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- For a fixed original graph satisfying the actual bijection formula, a
supplied inside-source step and the proved outside-source step yield the
exact strong candidate-induction schema. Names 0,1,6 remain free parameters. -/
def guarded_global_step_of_inside
    (inside : KDerivation (imp bijectionFormula.encode (imp (successorCode 8 10 15)
      (imp (member 0 8)
        (imp (replace 30 8 predicate).encode (replace 30 10 predicate).encode))))) :
    KDerivation (imp bijectionFormula.encode
      (allCode 31 (allStepsCode 31 30 8 10 15 32 33 predicate))) := by
  let B := bijectionFormula.encode
  let P := (replace 30 8 predicate).encode
  let Q := (replace 30 10 predicate).encode
  let S := successorCode 8 10 15
  let C := predecessorCore 31 8 10 15 32 33
  let Γ := [B]
  have hb : Context Γ B := Context.head [] B
  have hs : Context Γ (imp S (imp P Q)) := .mp hb (.closed (guarded_successor_of_inside inside))
  have hp : Context Γ (imp C (imp P Q)) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := [P,C,B]
    have hP : Context Δ P := Context.head _ _
    have hC : Context Δ C := .hypothesis (by simp [Δ])
    have hS : Context Δ S := Context.conjunctionLeft (Context.conjunctionRight hC)
    exact .mp hP (.mp hS (Context.under (Context.under hs C) P))
  have hv (v : Nat) (fresh : v ∉ bijectionFormula.names) :
      ∀ q, q ∈ Γ → KDerivation (imp q (allCode v q)) := by
    intro q hq
    have he : q = B := by simpa [Γ] using hq
    subst q
    exact bijectionFormula.vacuity v fresh
  have hall := Context.generalize 31 (hv 31 (by decide))
    (Context.generalize 10 (hv 10 (by decide))
      (Context.generalize 8 (hv 8 (by decide)) hp))
  apply Context.closeEmpty
  apply Context.deduction
  exact hall

theorem guarded_global_step_of_inside_certificate
    (inside : KDerivation (imp bijectionFormula.encode (imp (successorCode 8 10 15)
      (imp (member 0 8)
        (imp (replace 30 8 predicate).encode (replace 30 10 predicate).encode))))) :
    theoremCode (certificate (guarded_global_step_of_inside inside)) =
      imp bijectionFormula.encode
        (allCode 31 (allStepsCode 31 30 8 10 15 32 33 predicate)) :=
  certificate_correct (guarded_global_step_of_inside inside)

end PASoundness.PAtoCompactPartialInverseGuardedGlobalStep

#print axioms PASoundness.PAtoCompactPartialInverseGuardedGlobalStep.guarded_global_step_of_inside
#print axioms PASoundness.PAtoCompactPartialInverseGuardedGlobalStep.guarded_global_step_of_inside_certificate
