import PASoundness.PeanoBetaUniformPreserve
import PASoundness.PeanoBetaCRTStep
import PASoundness.PeanoPolynomialQuotient

/-! Base invariant ingredients for bounded beta CRT inside PA. The processed
prefix is zero and the product is one. This module does not assert the CRT
successor step, bounded CRT, or beta-trace existence. -/
namespace PASoundness.PeanoBetaCRTBase
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoDivisibility

/-- With processed prefix N=0, every demanded prior row is vacuous. `φ` is an
arbitrary object-level PA relation whose names 2 and 3 are bound here. The
existential row form does not require the relation to select a unique value. -/
def emptyRows (φ : Peano.Formula) : Peano.Formula :=
  FOL.allAt 2 ((less (.var 2) zero).imp
    (FOL.existsAt 3 (φ ⊓ (beta zero (.var 1) (.var 2) (.var 3)))))

/-- With product P=1 and processed prefix N=0, earlier modulus divisibility is
vacuous. The beta parameter is free name 1. -/
def emptyDivisors : Peano.Formula :=
  FOL.allAt 2 ((less (.var 2) zero).imp
    (divides (modulus (.var 1) (.var 2)) (succ zero)))

/-- PA derives the empty row and divisor components for any formula `φ`. -/
theorem empty_prefix (φ : Peano.Formula) : FormulaProves (emptyRows φ ⊓ emptyDivisors) := by
  have hrow : FormulaProves (emptyRows φ) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.generalize 2
    · intro ψ hψ
      simp at hψ
    apply FOL.Context.deduction
    exact FOL.Context.explode _
      (.mp (.closed (PeanoEmptyBitSet.no_less_zero (.var 2))) (FOL.Context.head [] _))
  have hdiv : FormulaProves emptyDivisors := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.generalize 2
    · intro ψ hψ
      simp at hψ
    apply FOL.Context.deduction
    exact FOL.Context.explode _
      (.mp (.closed (PeanoEmptyBitSet.no_less_zero (.var 2))) (FOL.Context.head [] _))
  apply FOL.Context.closeEmpty
  exact FOL.Context.conjunctionIntro (.closed hrow) (.closed hdiv)

/-- With product 1, the concrete witnesses u=1 and v=0 give an inverse
certificate against every beta modulus, inside the syntactic PA calculus. -/
theorem one_inverse_equation (c j : Peano.Term) :
    FormulaProves ((mul (succ zero) (succ zero)).equal
      (add (succ zero) (mul zero (modulus c j)))) := by
  apply PeanoPolynomialQuotient.cls_exact
  simp only [PeanoPolynomialQuotient.cls_mul, PeanoPolynomialQuotient.cls_add, PeanoPolynomialQuotient.cls_one, PeanoPolynomialQuotient.cls_zero]
  ring

/-- Parameter is free variable 1, future index is variable 2 and inverse
witnesses are variables 3,4. The leading product is exactly one. -/
def baseInverseBody (u v : Peano.Term) : Peano.Formula :=
  (mul (succ zero) u).equal (add (succ zero) (mul v (modulus (.var 1) (.var 2))))

def baseInverse : Peano.Formula :=
  FOL.existsAt 3 (FOL.existsAt 4 (baseInverseBody (.var 3) (.var 4)))

/-- PA constructs the explicit witnesses u=1 and v=0 for the fixed-name
future modulus. No bound or positivity hypothesis is needed. -/
theorem base_inverse_vars : FormulaProves baseInverse := by
  let one := succ zero
  let z := zero
  have heq : FormulaProves (baseInverseBody one z) := by
    simpa only [baseInverseBody, one, z] using one_inverse_equation (.var 1) (.var 2)
  let inner := baseInverseBody one (.var 4)
  have hs : FOL.substAt inner 4 z = baseInverseBody one z := by
    simp [FOL.substAt, inner, baseInverseBody, one, z, FOL.equality_subst,
      add_subst, mul_subst, modulus, succ_subst, PeanoArithmetic.zero_subst,
      FirstOrder.Language.Term.subst]
  have h₄ : FormulaProves (FOL.existsAt 4 inner) := by
    apply FOL.Derivation.mp (FOL.Derivation.existsIntro (A := Peano.Axiom) inner 4 z)
    rw [hs]
    exact heq
  have hs' : FOL.substAt (FOL.existsAt 4 (baseInverseBody (.var 3) (.var 4))) 3 one =
      FOL.existsAt 4 inner := by
    simp [FOL.substAt, inner, baseInverseBody, one, FOL.existsAt, FOL.allAt,
      modulus, Peano.add, Peano.mul, Peano.succ, Peano.zero,
      FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
      FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.relabelAux]
    repeat' first
      | rfl
      | constructor
      | (congr 1; funext i; fin_cases i <;>
          dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])
  unfold baseInverse
  apply FOL.Derivation.mp (FOL.Derivation.existsIntro
    (FOL.existsAt 4 (baseInverseBody (.var 3) (.var 4))) 3 one)
  rw [hs']
  exact h₄

/-- PA proves inverse certificates for product one for every future index,
with an arbitrary free beta parameter in variable 1. -/
theorem base_inverse_all : FormulaProves (FOL.allAt 2 baseInverse) :=
  .generalize 2 base_inverse_vars


/-- The instantiated base invariant: B=0, P=1, no processed rows and an
inverse certificate for every future modulus. The relation need not be
functional, and no induction step is claimed. -/
def baseInvariant (φ : Peano.Formula) : Peano.Formula :=
  (emptyRows φ ⊓ emptyDivisors) ⊓ FOL.allAt 2 baseInverse

/-- PA constructs the full base invariant for any object-level relation φ. -/
theorem base_invariant (φ : Peano.Formula) : FormulaProves (baseInvariant φ) := by
  apply FOL.Context.closeEmpty
  exact FOL.Context.conjunctionIntro (.closed (empty_prefix φ)) (.closed base_inverse_all)

end PASoundness.PeanoBetaCRTBase
