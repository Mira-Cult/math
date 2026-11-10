import PASoundness.Peano
import PASoundness.FOLQuantifierDerivations

/-!
# Initial internal PA arithmetic derivations

These are actual finite proofs in the displayed PA calculus, independently of
PA's metatheoretic soundness. The left-zero addition law below uses full
first-order induction, equality substitution, the two addition axioms, and
logical rules. This is a small reusable component of the later internal
arithmetic coding development; it does not yet prove beta uniqueness, power
growth, bit-position bounds, or finite comprehension.
-/
namespace PASoundness.PeanoArithmetic
open FirstOrder FirstOrder.Language
open Peano

@[simp] theorem zero_subst (σ : Nat → Peano.Term) : zero.subst σ = zero := by
  unfold zero
  simp only [Term.subst]
  congr 1
  funext i
  exact Fin.elim0 i

@[simp] theorem succ_subst (t : Peano.Term) (σ : Nat → Peano.Term) :
    (succ t).subst σ = succ (t.subst σ) := by
  unfold succ
  simp only [Term.subst]
  congr 1
  funext i
  have he : i = 0 := Fin.eq_of_val_eq (by have h := i.isLt; omega)
  subst i
  rfl

@[simp] theorem add_subst (t u : Peano.Term) (σ : Nat → Peano.Term) :
    (add t u).subst σ = add (t.subst σ) (u.subst σ) := by
  unfold add
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
private def leftZeroFormula : Peano.Formula := (add zero x).equal x

private theorem leftZero_base :
    FormulaProves (FOL.substAt leftZeroFormula 0 zero) := by
  simpa only [FOL.substAt, leftZeroFormula, FOL.equality_subst, add_subst,
    zero_subst, x, Term.subst, ↓reduceIte] using
    (FOL.Derivation.axiom (Axiom.add_zero zero))

private theorem leftZero_step :
    FormulaProves (leftZeroFormula.imp
      (FOL.substAt leftZeroFormula 0 (succ x))) := by
  have congruence : FormulaProves
      (leftZeroFormula.imp
        (((succ (add zero x)).equal (succ (add zero x))).imp
          ((succ (add zero x)).equal (succ x)))) := by
    have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
      (FOL.LogicalAxiom.eqSubst
        ((succ (add zero x)).equal (succ parameter)) 1 (add zero x) x)
    simpa only [FOL.substAt, FOL.equality_subst, succ_subst, add_subst,
      zero_subst, x, parameter, Term.subst, if_neg (by decide : (0:Nat) ≠ 1), ↓reduceIte, leftZeroFormula] using h
  have transport : FormulaProves
      (((succ (add zero x)).equal (succ x)).imp
        (((add zero (succ x)).equal (succ (add zero x))).imp
          ((add zero (succ x)).equal (succ x)))) := by
    have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
      (FOL.LogicalAxiom.eqSubst
        ((add zero (succ x)).equal parameter) 1 (succ (add zero x)) (succ x))
    simpa only [FOL.substAt, FOL.equality_subst, succ_subst, add_subst,
      zero_subst, x, parameter, Term.subst, if_neg (by decide : (0:Nat) ≠ 1), ↓reduceIte] using h
  have step : FormulaProves
      (leftZeroFormula.imp ((add zero (succ x)).equal (succ x))) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have hs : FOL.Context Peano.Axiom [leftZeroFormula]
        ((succ (add zero x)).equal (succ x)) :=
      .mp (.mp (.closed congruence) (FOL.Context.head [] leftZeroFormula))
        (.closed (.logical (.eqRefl _)))
    exact .mp (.mp (.closed transport) hs) (.closed (.axiom (.add_succ zero x)))
  simpa only [FOL.substAt, leftZeroFormula, FOL.equality_subst, add_subst,
    zero_subst, x, Term.subst, ↓reduceIte] using step

/-- A genuine universally quantified PA theorem proved by its induction schema. -/
theorem zero_add_all :
    FormulaProves (FOL.allAt 0 ((add zero (.var 0)).equal (.var 0))) :=
  .mp (.mp (.axiom (.induction leftZeroFormula 0)) leftZero_base)
    (.generalize 0 leftZero_step)

/-- Every arithmetic term can be substituted by an ordinary all-elimination
instance; the result is still an actual PA derivation. -/
theorem zero_add (t : Peano.Term) : FormulaProves ((add zero t).equal t) := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (FOL.LogicalAxiom.allElim ((add zero (.var 0)).equal (.var 0)) 0 t)) zero_add_all
  simpa only [FOL.substAt, FOL.equality_subst, add_subst, zero_subst,
    Term.subst, ↓reduceIte] using h

end PASoundness.PeanoArithmetic
