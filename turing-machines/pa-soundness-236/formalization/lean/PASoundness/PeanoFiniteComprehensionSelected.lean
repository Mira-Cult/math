import PASoundness.PeanoPowerAppendSuccessor
import PASoundness.PeanoBitInsertion

/-! The selected branch's next power, code bound, and newly set bit. -/
namespace PASoundness.PeanoFiniteComprehensionSelected
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

/-- The literal power-successor derivation with power name 2, matching the
finite-comprehension invariant. -/
theorem successor_power : FormulaProves
    ((pow2 (.var 0) (.var 2)).imp
      (pow2 (succ (.var 0)) (add (.var 2) (.var 2)))) := by
  let φ := (pow2 (.var 0) (.var 6)).imp
    (pow2 (succ (.var 0)) (add (.var 6) (.var 6)))
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim φ 6 (.var 2)))
    (.generalize 6 PeanoPowerAppendSuccessor.power_successor)
  simpa [φ, FOL.substAt, subst_imp, pow2_subst, succ_subst, add_subst,
    FirstOrder.Language.Term.subst] using h

/-- Given a power and a code strictly below it, PA derives the next power,
the strict upper bound for the selected code `p+a`, and the new bit at the
old endpoint. This does not assert the selector predicate, preserve earlier
bits, or construct the complete comprehension invariant. -/
theorem selected_code_properties : FormulaProves
    ((pow2 (.var 0) (.var 2)).imp
      ((less (.var 3) (.var 2)).imp
        ((pow2 (succ (.var 0)) (add (.var 2) (.var 2))) ⊓
          ((less (add (.var 2) (.var 3)) (add (.var 2) (.var 2))) ⊓
            (bitFormula (add (.var 2) (.var 3)) (.var 0)))))) := by
  let P := pow2 (.var 0) (.var 2)
  let L := less (.var 3) (.var 2)
  let Γ := [L,P]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ L := .head _ _
  have hnext : FOL.Context Peano.Axiom Γ
      (pow2 (succ (.var 0)) (add (.var 2) (.var 2))) := .mp (.closed successor_power) hp
  have hbound : FOL.Context Peano.Axiom Γ
      (less (add (.var 2) (.var 3)) (add (.var 2) (.var 2))) :=
    .mp (.closed (PeanoMultiplyQuotientStep.less_add_left (.var 3) (.var 2) (.var 2))) hl
  have hbit : FOL.Context Peano.Axiom Γ
      (bitFormula (add (.var 2) (.var 3)) (.var 0)) :=
    .mp (.mp (.closed (PeanoBitInsertion.inserted_bit (.var 0) (.var 2) (.var 3))) hp) hl
  exact FOL.Context.conjunctionIntro hnext (FOL.Context.conjunctionIntro hbound hbit)

end PASoundness.PeanoFiniteComprehensionSelected

#print axioms PASoundness.PeanoFiniteComprehensionSelected.successor_power
#print axioms PASoundness.PeanoFiniteComprehensionSelected.selected_code_properties
