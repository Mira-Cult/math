import PASoundness.PAtoCompactProductOutputOutsidePathLift
import PASoundness.PAtoCompactFreeVacuity

/-! Outside-source successor step for the guarded transported-triple graph.
The same graph witness is retained; the inside-source branch remains open. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputOutsideStep

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactProductOutputPartialBase PASoundness.PAtoCompactProductOutputOutsidePath
open PASoundness.PAtoCompactProductOutputOutsidePathLift

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def oldInvariant : Formula := replace 59 74 partialInvariant
def oldPoint : Formula := .imp endpointGuard
  (namedBoth (.imp targetTriple oldPath) (.imp oldPath targetTriple))

theorem old_invariant_shape : oldInvariant = .all 56 (.all 57 (.all 60 oldPoint)) := by decide
theorem old_instance_shape : replace 64 74 predicate = .ex 58 oldInvariant := by decide
theorem next_instance_shape : replace 64 59 predicate = .ex 58 partialInvariant := by decide

def old_instance : KDerivation (imp oldInvariant.encode oldPoint.encode) := by
  have h56 := allSpecialize 56 (.all 57 (.all 60 oldPoint)) (by decide)
  have h57 := allSpecialize 57 (.all 60 oldPoint) (by decide)
  have h60 := allSpecialize 60 oldPoint (by decide)
  rw [old_invariant_shape]
  simpa [Formula.encode] using compose h56 (compose h57 h60)

def outside_successor : KDerivation (imp guard.encode
    (imp oldInvariant.encode partialInvariant.encode)) := by
  let Γ := [oldInvariant.encode,guard.encode]
  have hpoint : Context Γ (imp endpointGuard.encode
      (both (imp targetTriple.encode pathAt.encode) (imp pathAt.encode targetTriple.encode))) := by
    apply Context.deduction
    let Δ := [endpointGuard.encode,oldInvariant.encode,guard.encode]
    have he : Context Δ endpointGuard.encode := .head _ _
    have ho : Context Δ oldInvariant.encode := .hypothesis (by simp [Δ])
    have hg : Context Δ guard.encode := .hypothesis (by simp [Δ])
    have hold := Context.mp ho (.closed old_instance)
    have hold' : Context Δ (imp endpointGuard.encode
        (both (imp targetTriple.encode oldPath.encode) (imp oldPath.encode targetTriple.encode))) := by
      simpa [oldPoint, namedBoth, Formula.not, Formula.encode, both, neg] using hold
    have hpair := Context.mp he hold'
    have hpath := Context.mp hg (.closed outside_path_equiv)
    have hpath' : Context Δ (both (imp pathAt.encode oldPath.encode) (imp oldPath.encode pathAt.encode)) := by
      simpa [next_path_shape] using hpath
    have hf : Context Δ (imp targetTriple.encode pathAt.encode) := by
      apply Context.deduction
      let Θ := [targetTriple.encode,endpointGuard.encode,oldInvariant.encode,guard.encode]
      have ht : Context Θ targetTriple.encode := .head _ _
      have ho₁ := Context.under (Context.conjunctionLeft hpair) targetTriple.encode
      have hp₁ := Context.under (Context.conjunctionRight hpath') targetTriple.encode
      exact Context.mp (Context.mp ht ho₁) hp₁
    have hb : Context Δ (imp pathAt.encode targetTriple.encode) := by
      apply Context.deduction
      let Θ := [pathAt.encode,endpointGuard.encode,oldInvariant.encode,guard.encode]
      have hp₀ : Context Θ pathAt.encode := .head _ _
      have hp₁ := Context.under (Context.conjunctionLeft hpath') pathAt.encode
      have ho₁ := Context.under (Context.conjunctionRight hpair) pathAt.encode
      exact Context.mp (Context.mp hp₀ hp₁) ho₁
    exact Context.conjunctionIntro hf hb
  have hv (v : Nat) (hO : v ∉ oldInvariant.free) (hG : v ∉ guard.names) :
      ∀ q, q ∈ Γ → KDerivation (imp q (allCode v q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = oldInvariant.encode
    · subst q; exact free_vacuity v oldInvariant hO
    · have he' : q = guard.encode := hq.resolve_left he
      subst q; exact guard.vacuity v hG
  have hall := Context.generalize 56 (hv 56 (by decide) (by decide))
    (Context.generalize 57 (hv 57 (by decide) (by decide))
      (Context.generalize 60 (hv 60 (by decide) (by decide)) hpoint))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  simpa [Γ, partialInvariant, namedBoth, Formula.not, Formula.encode, both, neg] using hall

/-- Lift the outside branch through the same graph58 witness. -/
def outside_predicate_step : KDerivation (imp guard.encode
    (imp (replace 64 74 predicate).encode (replace 64 59 predicate).encode)) := by
  have hlift := conditionalExistsCongr 58 (guard.vacuity 58 (by decide)) outside_successor
  simpa [old_instance_shape, next_instance_shape, Formula.encode] using hlift

theorem outside_predicate_step_certificate : theoremCode (certificate outside_predicate_step) =
    imp guard.encode (imp (replace 64 74 predicate).encode (replace 64 59 predicate).encode) := certificate_correct _

end PASoundness.PAtoCompactProductOutputOutsideStep

#print axioms PASoundness.PAtoCompactProductOutputOutsideStep.outside_successor
#print axioms PASoundness.PAtoCompactProductOutputOutsideStep.outside_predicate_step
#print axioms PASoundness.PAtoCompactProductOutputOutsideStep.outside_predicate_step_certificate
