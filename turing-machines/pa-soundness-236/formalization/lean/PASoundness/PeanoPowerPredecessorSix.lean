import PASoundness.PeanoPowerPredecessor
import PASoundness.PeanoBetaCRTAlpha

/-! Capture-safe predecessor naming for the power-divisibility induction. -/
namespace PASoundness.PeanoPowerPredecessorSix
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaCRTAlpha

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not]
  change ((φ.subst σ).imp (ψ.not.subst σ)).not = _
  rw [subst_not]

def predecessorRow (r : Peano.Term) : Peano.Formula :=
  (pow2 (.var 0) r) ⊓ ((.var 6 : Peano.Term).equal (add r r))

private theorem renamed_source :
    FOL.substAt PeanoPowerPredecessor.predecessorPower 1 (.var 6) =
      FOL.existsAt 5 (predecessorRow (.var 5)) := by
  unfold PeanoPowerPredecessor.predecessorPower
  rw [subst_var_existsAt _ 1 6 5 (by decide) (by decide)]
  simp [FOL.substAt, predecessorRow, subst_and, pow2_subst, FOL.equality_subst,
    add_subst, FirstOrder.Language.Term.subst]

/-- PA obtains a predecessor power at free exponent name 0, with output 6
and a fresh predecessor witness 8. -/
theorem predecessor_six_eight : FormulaProves
    ((pow2 (succ (.var 0)) (.var 6)).imp (FOL.existsAt 8 (predecessorRow (.var 8)))) := by
  let φ : Peano.Formula :=
    (pow2 (succ (.var 0)) (.var 1)).imp PeanoPowerPredecessor.predecessorPower
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim φ 1 (.var 6)))
    (.generalize 1 PeanoPowerPredecessor.power_successor_predecessor)
  have h₁ : FormulaProves ((pow2 (succ (.var 0)) (.var 6)).imp
      (FOL.existsAt 5 (predecessorRow (.var 5)))) := by
    have hs : FOL.substAt φ 1 (.var 6) =
        (pow2 (succ (.var 0)) (.var 6)).imp
          (FOL.existsAt 5 (predecessorRow (.var 5))) := by
      change ((pow2 (succ (.var 0)) (.var 1)).subst
        (fun y => if y = 1 then .var 6 else .var y)).imp
          (FOL.substAt PeanoPowerPredecessor.predecessorPower 1 (.var 6)) = _
      rw [renamed_source]
      simp [pow2_subst, succ_subst, FirstOrder.Language.Term.subst]
    rw [hs] at h
    exact h
  have hf : 8 ∉ (predecessorRow (.var 5)).freeVarFinset := by decide
  have ha := exists_alpha_forward (predecessorRow (.var 5)) 5 8 (by decide) hf
  have hs : FOL.substAt (predecessorRow (.var 5)) 5 (.var 8) =
      predecessorRow (.var 8) := by
    simp [FOL.substAt, predecessorRow, subst_and, pow2_subst, FOL.equality_subst,
      add_subst, FirstOrder.Language.Term.subst]
  rw [hs] at ha
  exact FOL.Derivation.compose h₁ ha

end PASoundness.PeanoPowerPredecessorSix

#print axioms PASoundness.PeanoPowerPredecessorSix.predecessor_six_eight
