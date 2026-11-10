import PASoundness.PeanoArithmetic
/-! Genuine PA derivations for left-zero multiplication. -/
namespace PASoundness.PeanoMultiplication
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic

@[simp] theorem mul_subst (t u : Peano.Term) (σ : Nat → Peano.Term) :
    (mul t u).subst σ = mul (t.subst σ) (u.subst σ) := by
  unfold mul
  simp only [Term.subst]
  congr 1
  funext i
  have h : i = 0 ∨ i = 1 := by
    have hi := i.isLt
    by_cases he : i.val = 0
    · exact Or.inl (Fin.eq_of_val_eq he)
    · exact Or.inr (Fin.eq_of_val_eq (by omega))
  rcases h with rfl | rfl <;> rfl

private def x : Peano.Term := .var 0
private def parameter : Peano.Term := .var 1
private def leftZeroFormula : Peano.Formula := (mul zero x).equal zero

private theorem leftZero_base :
    FormulaProves (FOL.substAt leftZeroFormula 0 zero) := by
  simpa only [FOL.substAt, leftZeroFormula, FOL.equality_subst, mul_subst,
    zero_subst, x, Term.subst, ↓reduceIte] using
    (FOL.Derivation.axiom (Axiom.mul_zero zero))

private theorem leftZero_step :
    FormulaProves (leftZeroFormula.imp
      (FOL.substAt leftZeroFormula 0 (succ x))) := by
  have trans1 : FormulaProves
      (((add (mul zero x) zero).equal (mul zero x)).imp
        (((mul zero (succ x)).equal (add (mul zero x) zero)).imp
          ((mul zero (succ x)).equal (mul zero x)))) := by
    have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
      (FOL.LogicalAxiom.eqSubst ((mul zero (succ x)).equal parameter) 1
        (add (mul zero x) zero) (mul zero x))
    simpa only [FOL.substAt, FOL.equality_subst, mul_subst, add_subst,
      succ_subst, zero_subst, x, parameter, Term.subst,
      if_neg (by decide : (0:Nat) ≠ 1), ↓reduceIte] using h
  have trans2 : FormulaProves
      (((mul zero x).equal zero).imp
        (((mul zero (succ x)).equal (mul zero x)).imp
          ((mul zero (succ x)).equal zero))) := by
    have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
      (FOL.LogicalAxiom.eqSubst ((mul zero (succ x)).equal parameter) 1 (mul zero x) zero)
    simpa only [FOL.substAt, FOL.equality_subst, mul_subst, add_subst,
      succ_subst, zero_subst, x, parameter, Term.subst,
      if_neg (by decide : (0:Nat) ≠ 1), ↓reduceIte] using h
  have step : FormulaProves
      (leftZeroFormula.imp ((mul zero (succ x)).equal zero)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have ht : FOL.Context Peano.Axiom [leftZeroFormula]
        ((mul zero (succ x)).equal (mul zero x)) :=
      .mp (.mp (.closed trans1) (.closed (.axiom (.add_zero (mul zero x)))))
        (.closed (.axiom (.mul_succ zero x)))
    exact .mp (.mp (.closed trans2) (FOL.Context.head [] leftZeroFormula)) ht
  simpa only [FOL.substAt, leftZeroFormula, FOL.equality_subst, mul_subst,
    zero_subst, x, Term.subst, ↓reduceIte] using step

/-- PA proves the universally quantified left-zero multiplication law. -/
theorem zero_mul_all :
    FormulaProves (FOL.allAt 0 ((mul zero (.var 0)).equal zero)) :=
  .mp (.mp (.axiom (.induction leftZeroFormula 0)) leftZero_base)
    (.generalize 0 leftZero_step)

/-- The law instantiated with an arbitrary first-order arithmetic term. -/
theorem zero_mul (t : Peano.Term) : FormulaProves ((mul zero t).equal zero) := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (FOL.LogicalAxiom.allElim ((mul zero (.var 0)).equal zero) 0 t)) zero_mul_all
  simpa only [FOL.substAt, FOL.equality_subst, mul_subst, zero_subst,
    Term.subst, ↓reduceIte] using h
end PASoundness.PeanoMultiplication
