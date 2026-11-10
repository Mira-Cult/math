import PASoundness.PeanoPowerDivisibilityInduction

/-! Instantiate the PA power-divisibility induction hypothesis at a fresh
predecessor output while retaining the original free endpoint. -/
namespace PASoundness.PeanoPowerDivisibilityInstantiate
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoDivisibility
open PeanoPowerDivisibilityInduction

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

private theorem divides_subst (k d : Peano.Term) (σ : Nat → Peano.Term) :
    (divides k d).subst σ = divides (k.subst σ) (d.subst σ) := by
  unfold divides
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1]

/-- In PA, the induction family at exponent 0 gives its instance at output
name 8. Names 1 and 2 retain their values; name 6 remains available for the
successor output. The induction family is an explicit premise. -/
theorem predecessor_instance : FormulaProves (family.imp
    ((pow2 (.var 1) (.var 2)).imp ((pow2 (.var 0) (.var 8)).imp
      ((less (.var 1) (.var 0)).imp
        (divides (add (.var 2) (.var 2)) (.var 8)))))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  let Γ := [family]
  have hf : FOL.Context Peano.Axiom Γ family := .head _ _
  have h1 : FOL.Context Peano.Axiom Γ
      (FOL.allAt 2 (FOL.allAt 6 (body (.var 0)))) := FOL.Context.allSelf hf
  have h2 : FOL.Context Peano.Axiom Γ (FOL.allAt 6 (body (.var 0))) :=
    FOL.Context.allSelf h1
  have h3 := FOL.Context.allElim h2 (.var 8)
  simpa [FOL.substAt, body, subst_imp, pow2_subst, less_subst, divides_subst,
    add_subst, FirstOrder.Language.Term.subst] using h3

end PASoundness.PeanoPowerDivisibilityInstantiate

#print axioms PASoundness.PeanoPowerDivisibilityInstantiate.predecessor_instance
