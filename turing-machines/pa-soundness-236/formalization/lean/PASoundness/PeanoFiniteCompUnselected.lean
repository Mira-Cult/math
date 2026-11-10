import PASoundness.PeanoPowerAppendSuccessor
import PASoundness.PeanoBitBelowPowerAll

/-! The unselected branch of one bounded-selector update. This is an
object-level PA derivation for the power, bound, and new-index bit facts; it
does not construct a selector or establish comprehension. -/
namespace PASoundness.PeanoFiniteCompUnselected
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

private theorem successor_at_power2 : FormulaProves
    ((pow2 (.var 0) (.var 2)).imp
      (pow2 (succ (.var 0)) (add (.var 2) (.var 2)))) := by
  let φ := (pow2 (.var 0) (.var 6)).imp
    (pow2 (succ (.var 0)) (add (.var 6) (.var 6)))
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim φ 6 (.var 2)))
    (.generalize 6 PeanoPowerAppendSuccessor.power_successor)
  simpa [φ, FOL.substAt, subst_imp, pow2_subst, add_subst, succ_subst,
    FirstOrder.Language.Term.subst] using h

/-- With n at 0, the old power at 2 and the old code at 3, retaining the code
and doubling the power preserves the strict code bound and leaves bit n unset. -/
theorem unselected_step : FormulaProves
    ((pow2 (.var 0) (.var 2)).imp
      ((less (.var 3) (.var 2)).imp
        ((pow2 (succ (.var 0)) (add (.var 2) (.var 2))) ⊓
          ((less (.var 3) (add (.var 2) (.var 2))) ⊓
            (bitFormula (.var 3) (.var 0)).not)))) := by
  let P := pow2 (.var 0) (.var 2)
  let B := less (.var 3) (.var 2)
  let Γ := [B,P]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ])
  have hb : FOL.Context Peano.Axiom Γ B := FOL.Context.head _ _
  have hs : FOL.Context Peano.Axiom Γ
      (pow2 (succ (.var 0)) (add (.var 2) (.var 2))) :=
    .mp (.closed successor_at_power2) hp
  have hl : FOL.Context Peano.Axiom Γ (less (.var 3) (add (.var 2) (.var 2))) :=
    .mp (.closed (PeanoQuotientGap.less_add_right (.var 3) (.var 2) (.var 2))) hb
  have hn : FOL.Context Peano.Axiom Γ (bitFormula (.var 3) (.var 0)).not :=
    .mp (.mp (.closed (PeanoBitBelowPowerAll.below_excludes_bit (.var 3) (.var 0) (.var 2))) hp) hb
  exact FOL.Context.conjunctionIntro hs (FOL.Context.conjunctionIntro hl hn)

end PASoundness.PeanoFiniteCompUnselected

#print axioms PASoundness.PeanoFiniteCompUnselected.unselected_step
