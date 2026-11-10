import PASoundness.PeanoFiniteComprehensionBase

/-! Boundary agreement for the unselected case of a bounded selector. -/
namespace PASoundness.PeanoFiniteCompUnselectedBoundary
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- The row agreement formula for the retained code `a`. -/
def agreement (φ : Peano.Formula) : Peano.Formula :=
  ((bitFormula (.var 3) (.var 1)).imp φ) ⊓
    (φ.imp (bitFormula (.var 3) (.var 1)))

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

/-- Substitution of the endpoint preserves the exact selector parameters. -/
theorem boundary_syntax (φ : Peano.Formula) :
    FOL.substAt (agreement φ) 1 (.var 0) =
      ((bitFormula (.var 3) (.var 0)).imp (FOL.substAt φ 1 (.var 0))) ⊓
      ((FOL.substAt φ 1 (.var 0)).imp (bitFormula (.var 3) (.var 0))) := by
  unfold FOL.substAt agreement
  rw [subst_and]
  simp only [subst_imp, bitFormula_subst,
    FirstOrder.Language.Term.subst, ↓reduceIte, show (3 : Nat) ≠ 1 by decide]

/-- From the selector's and the retained bit's negations at n, PA proves
their endpoint agreement. No bounded family or selector existence is assumed. -/
theorem unselected_boundary (φ : Peano.Formula) : FormulaProves
    ((FOL.substAt φ 1 (.var 0)).not.imp
      ((bitFormula (.var 3) (.var 0)).not.imp
        (FOL.substAt (agreement φ) 1 (.var 0)))) := by
  rw [boundary_syntax]
  let F := FOL.substAt φ 1 (.var 0)
  let B := bitFormula (.var 3) (.var 0)
  let Γ := [B.not,F.not]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hf : FOL.Context Peano.Axiom Γ F.not := .hypothesis (by simp [Γ])
  have hb : FOL.Context Peano.Axiom Γ B.not := .head _ _
  have hforward : FOL.Context Peano.Axiom Γ (B.imp F) := by
    apply FOL.Context.deduction
    exact FOL.Context.explode F
      (.mp (FOL.Context.under hb B) (FOL.Context.head Γ B))
  have hback : FOL.Context Peano.Axiom Γ (F.imp B) := by
    apply FOL.Context.deduction
    exact FOL.Context.explode B
      (.mp (FOL.Context.under hf F) (FOL.Context.head Γ F))
  exact FOL.Context.conjunctionIntro hforward hback

end PASoundness.PeanoFiniteCompUnselectedBoundary

#print axioms PASoundness.PeanoFiniteCompUnselectedBoundary.unselected_boundary
