import PASoundness.PeanoFiniteComprehensionBase

/-! Boundary agreement for the selected case of a bounded selector. -/
namespace PASoundness.PeanoFiniteCompSelectedBoundary
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- The row-agreement formula for the selected code `p+a`. -/
def agreement (φ : Peano.Formula) : Peano.Formula :=
  ((bitFormula (add (.var 2) (.var 3)) (.var 1)).imp φ) ⊓
    (φ.imp (bitFormula (add (.var 2) (.var 3)) (.var 1)))

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
  rfl

/-- The actual capture-safe endpoint instance uses index `n` in both the
selector and the bit; arbitrary parameters in the selector are retained. -/
theorem boundary_syntax (φ : Peano.Formula) :
    FOL.substAt (agreement φ) 1 (.var 0) =
      ((bitFormula (add (.var 2) (.var 3)) (.var 0)).imp
        (FOL.substAt φ 1 (.var 0))) ⊓
      ((FOL.substAt φ 1 (.var 0)).imp
        (bitFormula (add (.var 2) (.var 3)) (.var 0))) := by
  unfold FOL.substAt agreement
  rw [subst_and]
  simp only [subst_imp, bitFormula_subst,
    add_subst, FirstOrder.Language.Term.subst, ↓reduceIte,
    show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide]

/-- If the selector holds at `n` and the new code has bit `n`, PA proves the
exact endpoint agreement required by bounded-family extension. -/
theorem selected_boundary (φ : Peano.Formula) : FormulaProves
    ((FOL.substAt φ 1 (.var 0)).imp
      ((bitFormula (add (.var 2) (.var 3)) (.var 0)).imp
        (FOL.substAt (agreement φ) 1 (.var 0)))) := by
  rw [boundary_syntax]
  let F := FOL.substAt φ 1 (.var 0)
  let B := bitFormula (add (.var 2) (.var 3)) (.var 0)
  let Γ := [B,F]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hf : FOL.Context Peano.Axiom Γ F := .hypothesis (by simp [Γ])
  have hb : FOL.Context Peano.Axiom Γ B := .head _ _
  have hforward : FOL.Context Peano.Axiom Γ (B.imp F) := by
    apply FOL.Context.deduction
    exact FOL.Context.under hf B
  have hback : FOL.Context Peano.Axiom Γ (F.imp B) := by
    apply FOL.Context.deduction
    exact FOL.Context.under hb F
  exact FOL.Context.conjunctionIntro hforward hback

end PASoundness.PeanoFiniteCompSelectedBoundary

#print axioms PASoundness.PeanoFiniteCompSelectedBoundary.selected_boundary
