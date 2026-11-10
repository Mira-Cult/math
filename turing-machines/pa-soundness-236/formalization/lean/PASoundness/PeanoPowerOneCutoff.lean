import PASoundness.PeanoEmptyBitSet
import PASoundness.PeanoOrderSuccessor
import PASoundness.PeanoPowerExistenceBase
import PASoundness.PeanoOneMul

/-! The discrete bound needed to construct the one-step power trace in PA. -/
namespace PASoundness.PeanoPowerOneCutoff
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private def cutoff : Peano.Formula :=
  (less (.var 0) (succ zero)).imp ((.var 0 : Peano.Term).equal zero)

private theorem cutoff_base : FormulaProves (FOL.substAt cutoff 0 zero) := by
  have he : FormulaProves ((zero : Peano.Term).equal zero) := .logical (.eqRefl zero)
  have h := FOL.Derivation.weakening he (less zero (succ zero))
  simpa [FOL.substAt, cutoff, subst_imp, less_subst, FOL.equality_subst,
    succ_subst, PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst] using h

private theorem cutoff_step : FormulaProves
    (cutoff.imp (FOL.substAt cutoff 0 (succ (.var 0)))) := by
  have hdesc : FormulaProves ((less (succ (.var 0)) (succ zero)).imp (less (.var 0) zero)) :=
    (PeanoOrderSuccessor.less_succ_iff (.var 0) zero).2
  have hnot : FormulaProves (less (succ (.var 0)) (succ zero)).not :=
    .mp (FOL.Derivation.contrapose hdesc) (PeanoEmptyBitSet.no_less_zero (.var 0))
  have hnext : FormulaProves
      ((less (succ (.var 0)) (succ zero)).imp ((succ (.var 0)).equal zero)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    exact FOL.Context.explode _ (.mp (.closed hnot) (FOL.Context.head [] _))
  have h := FOL.Derivation.weakening hnext cutoff
  simpa [FOL.substAt, cutoff, subst_imp, less_subst, FOL.equality_subst,
    succ_subst, PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst] using h

/-- PA proves that every natural strictly below one equals zero. -/
theorem less_one_implies_zero (t : Peano.Term) :
    FormulaProves ((less t (succ zero)).imp (t.equal zero)) := by
  have hall : FormulaProves (FOL.allAt 0 cutoff) :=
    .mp (.mp (.axiom (.induction cutoff 0)) cutoff_base) (.generalize 0 cutoff_step)
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim cutoff 0 t)) hall
  simpa [FOL.substAt, cutoff, subst_imp, less_subst, FOL.equality_subst,
    succ_subst, PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst] using h

private theorem mul_right_congr (left u v : Peano.Term) :
    FormulaProves ((u.equal v).imp ((mul left u).equal (mul left v))) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term (add left u)
  have hi' : i ∉ left.varFinset ∧ i ∉ u.varFinset := by
    simpa [Peano.add, FirstOrder.Language.Term.varFinset] using hi
  let φ : Peano.Formula := (mul left u).equal (mul left (.var i))
  have h₀ : FOL.substAt φ i u = (mul left u).equal (mul left u) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, PeanoMultiplication.mul_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh left i u hi'.1, FOL.term_subst_fresh u i u hi'.2]
  have h₁ : FOL.substAt φ i v = (mul left u).equal (mul left v) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, PeanoMultiplication.mul_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh left i v hi'.1, FOL.term_subst_fresh u i v hi'.2]
  have h := FOL.Derivation.logical (Axiom := Peano.Axiom) (FOL.LogicalAxiom.eqSubst φ i u v)
  rw [h₀, h₁] at h
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  exact .mp (.mp (.closed h) (FOL.Context.head [] (u.equal v)))
    (.closed (.logical (.eqRefl _)))

private def one : Peano.Term := succ zero
private def two : Peano.Term := succ one
private def three : Peano.Term := succ two
private def five : Peano.Term := add (add two two) one

private theorem first_modulus : FormulaProves ((modulus one zero).equal two) := by
  exact .mp (PeanoOrderIrreflexive.succ_congr _ _) (PeanoMultiplication.mul_one one)

private theorem second_modulus : FormulaProves ((modulus one one).equal three) := by
  exact .mp (PeanoOrderIrreflexive.succ_congr _ _) (PeanoMultiplication.mul_one two)

private theorem first_remainder_bound : FormulaProves (less one (modulus one zero)) := by
  exact .mp (.mp (PeanoMultiplyQuotientStep.less_right_congr one two (modulus one zero))
    (FOL.Derivation.eqSymm first_modulus)) (PeanoPowerTransition.self_less_succ one)

private theorem second_remainder_bound : FormulaProves (less two (modulus one one)) := by
  exact .mp (.mp (PeanoMultiplyQuotientStep.less_right_congr two three (modulus one one))
    (FOL.Derivation.eqSymm second_modulus)) (PeanoPowerTransition.self_less_succ two)

/-- Concrete beta rows of the length-one doubling trace, using a shared code
`b=(2+2)+1`, `c=1` and displayed quotient witnesses 2 and 1. -/
theorem beta_one_step_rows :
    FormulaProves (beta five one zero one) ∧ FormulaProves (beta five one one two) := by
  have hprod : FormulaProves ((mul two (modulus one zero)).equal (add two two)) := by
    have h₁ := FOL.Derivation.mp (mul_right_congr two (modulus one zero) two) first_modulus
    have h₂ := FOL.Derivation.axiom (Peano.Axiom.mul_succ two one)
    have h₃ := FOL.Derivation.mp (PeanoAdditionAssociative.add_left_congr two (mul two one) two)
      (PeanoMultiplication.mul_one two)
    exact FOL.Derivation.eqTrans (FOL.Derivation.eqTrans h₁ h₂) h₃
  have hrow₀ : FormulaProves (five.equal (add (mul two (modulus one zero)) one)) :=
    FOL.Derivation.eqSymm (.mp (PeanoAdditionAssociative.add_left_congr one _ _) hprod)
  have heq : FormulaProves (five.equal (add three two)) :=
    FOL.Derivation.eqTrans (PeanoArithmetic.add_one (add two two))
      (FOL.Derivation.eqSymm (PeanoAdditionAssociative.add_succ_left two two))
  have hprod₁ : FormulaProves ((add (mul one (modulus one one)) two).equal (add three two)) := by
    have h₁ := FOL.Derivation.mp
      (PeanoAdditionAssociative.add_left_congr two (mul one (modulus one one)) (modulus one one))
      (PeanoArithmetic.one_mul (modulus one one))
    have h₂ := FOL.Derivation.mp (PeanoAdditionAssociative.add_left_congr two (modulus one one) three)
      second_modulus
    exact FOL.Derivation.eqTrans h₁ h₂
  have hrow₁ : FormulaProves (five.equal (add (mul one (modulus one one)) two)) :=
    FOL.Derivation.eqTrans heq (FOL.Derivation.eqSymm hprod₁)
  exact ⟨.mp (.mp (PeanoPowerExistenceBase.beta_intro five one zero one two) hrow₀) first_remainder_bound,
    .mp (.mp (PeanoPowerExistenceBase.beta_intro five one one two one) hrow₁) second_remainder_bound⟩

end PASoundness.PeanoPowerOneCutoff
