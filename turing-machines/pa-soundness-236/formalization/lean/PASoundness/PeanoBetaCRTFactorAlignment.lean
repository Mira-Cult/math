import PASoundness.PeanoBetaCRTAlignment
import PASoundness.PeanoBetaBoundedDivisibility

/-! The factor component of one PA CRT invariant update. The current factor
family remains an explicit hypothesis; no inverse, row or CRT existence is
asserted here. -/
namespace PASoundness.PeanoBetaCRTFactorAlignment
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoDivisibility
open PeanoBetaCRTInvariant PeanoBetaCRTAlignment

/-- Source next-product factor formula with product 4, boundary 6 and index 2. -/
def sourceNextFactors : Peano.Formula :=
  FOL.allAt 2 ((less (.var 2) (succ (.var 6))).imp
    (divides (modulus (.var 1) (.var 2)) (mul (.var 4) (modulus (.var 1) (.var 6)))))

/-- Exact factor condition for the updated product in invariant names. -/
def alignedFactors : Peano.Formula :=
  FOL.allAt 2 ((less (.var 2) (succ (.var 7))).imp
    (divides (modulus (.var 1) (.var 2)) alignedProduct))

private theorem divides_subst (k d : Peano.Term) (σ : Nat → Peano.Term) :
    (divides k d).subst σ = divides (k.subst σ) (d.subst σ) := by
  unfold divides
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1]

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

/-- Renaming the source successor-factor family yields exactly the updated
product family in invariant names. -/
theorem sourceNextFactors_alignment : sourceNextFactors.subst align = alignedFactors := by
  unfold sourceNextFactors alignedFactors
  simp only [align_all_two, subst_imp, less_subst, succ_subst, divides_subst, mul_subst,
    modulus, FirstOrder.Language.Term.subst, align, alignedProduct, ↓reduceIte]
  simp

/-- The two output substitutions reduce the invariant's next-factor clause
to the exact updated-product factor family. -/
theorem nextFactors_alignment :
    FOL.substAt (FOL.substAt nextFactors 11 alignedCode) 12 alignedProduct = alignedFactors := by
  have h11 : 11 ∉ nextFactors.freeVarFinset := by decide
  rw [substAt_fresh _ _ _ h11]
  let σ : Nat → Peano.Term := fun x => if x = 12 then alignedProduct else .var x
  have hfix : σ 2 = .var 2 := by simp [σ]
  have havoid : ∀ x, x ≠ 2 → 2 ∉ (σ x).varFinset := by
    intro x hx
    by_cases he : x = 12
    · subst x
      simp [σ, alignedProduct, modulus, mul, succ, FirstOrder.Language.Term.varFinset]
    · simp [σ, he, FirstOrder.Language.Term.varFinset, Ne.symm hx]
  change (FOL.allAt 2 ((less (.var 2) (succ (.var 7))).imp
    (divides (modulus (.var 1) (.var 2)) (.var 12)))).subst σ = _
  rw [arbitrary_subst_all_at σ 2 hfix havoid]
  simp [alignedFactors, subst_imp, divides_subst, less_subst, σ, modulus, mul_subst, succ_subst,
    FirstOrder.Language.Term.subst]

/-- Transport the PA source derivation once the exact syntax alignment is
supplied; this local parameter is eliminated by the theorem below. -/
theorem product_factors_of_alignment
    (hnext : sourceNextFactors.subst align = alignedFactors) :
    FormulaProves ((factorsAt (.var 7) 10).imp alignedFactors) := by
  have h := align_proves _ PeanoBetaBoundedDivisibility.bounded_divides_next_product
  change FormulaProves ((PeanoBetaUniformPreserve.boundedDivisors.imp sourceNextFactors).subst align) at h
  simpa only [subst_imp, factors_alignment, hnext] using h

/-- Logical packaging of the factor clause under an arbitrary retained side
condition and arbitrary selected-witness formula. -/
theorem component_of_alignments (φ side selected : Peano.Formula)
    (hnext : sourceNextFactors.subst align = alignedFactors)
    (htarget : FOL.substAt (FOL.substAt nextFactors 11 alignedCode) 12 alignedProduct =
      alignedFactors) :
    FormulaProves (side.imp ((currentMatrix φ).imp (selected.imp
      (FOL.substAt (FOL.substAt nextFactors 11 alignedCode) 12 alignedProduct)))) := by
  rw [htarget]
  let C := currentMatrix φ
  let Γ := [selected, C, side]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hc : FOL.Context Peano.Axiom Γ C := .hypothesis (by simp [Γ])
  have hf : FOL.Context Peano.Axiom Γ (factorsAt (.var 7) 10) :=
    FOL.Context.conjunctionRight (FOL.Context.conjunctionLeft hc)
  exact .mp (.closed (product_factors_of_alignment hnext)) hf

/-- From the old factor family, PA derives the updated factor family for
`P*modulus(C,k)` through the successor boundary. -/
theorem product_factors : FormulaProves ((factorsAt (.var 7) 10).imp alignedFactors) :=
  product_factors_of_alignment sourceNextFactors_alignment

/-- Exact factor component for the dependent CRT wrapper. The side and selected
formulas are retained as arbitrary antecedents; this factor proof does not use
them, or require predicate freshness. -/
theorem factors_component (φ side selected : Peano.Formula) :
    FormulaProves (side.imp ((currentMatrix φ).imp (selected.imp
      (FOL.substAt (FOL.substAt nextFactors 11 alignedCode) 12 alignedProduct)))) :=
  component_of_alignments φ side selected sourceNextFactors_alignment nextFactors_alignment

end PASoundness.PeanoBetaCRTFactorAlignment
