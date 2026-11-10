import PASoundness.PeanoAddition
import PASoundness.PeanoMultiplication
/-! Syntactic left-one multiplication, for arbitrary arithmetic terms. -/
namespace PASoundness.PeanoArithmetic
open FirstOrder FirstOrder.Language
open Peano PeanoMultiplication

theorem add_congruence_left {A : Peano.Formula → Prop} (a b c : Peano.Term) :
    FOL.Derivation A ((a.equal b).imp ((add a c).equal (add b c))) := by
  let x := (b.varFinset ∪ c.varFinset).sup id + 1
  have hx : x ∉ b.varFinset ∪ c.varFinset := by
    intro hmem
    have hle : x ≤ (b.varFinset ∪ c.varFinset).sup id := Finset.le_sup (f := id) hmem
    dsimp [x] at hle
    omega
  have hb : x ∉ b.varFinset := fun h => hx (Finset.mem_union_left _ h)
  have hc : x ∉ c.varFinset := fun h => hx (Finset.mem_union_right _ h)
  let φ : Peano.Formula := (add (.var x) c).equal (add b c)
  have h₀ : FOL.substAt φ x b = (add b c).equal (add b c) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, add_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte]
    rw [FOL.term_subst_fresh c x b hc, FOL.term_subst_fresh b x b hb]
  have h₁ : FOL.substAt φ x a = (add a c).equal (add b c) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, add_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte]
    rw [FOL.term_subst_fresh c x a hc, FOL.term_subst_fresh b x a hb]
  have h := FOL.Derivation.logical (Axiom := A) (FOL.LogicalAxiom.eqSubst φ x b a)
  rw [h₀, h₁] at h
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hs : FOL.Context A [a.equal b] (b.equal a) := FOL.Context.eqSymm (FOL.Context.head [] (a.equal b))
  exact .mp (.mp (.closed h) hs) (.closed (.logical (.eqRefl _)))

private def one : Peano.Term := succ zero
private def x : Peano.Term := .var 0
private def oneMulFormula : Peano.Formula := (mul one x).equal x

private theorem oneMul_base : FormulaProves (FOL.substAt oneMulFormula 0 zero) := by
  simpa only [FOL.substAt, oneMulFormula, FOL.equality_subst, mul_subst, succ_subst,
    zero_subst, x, one, Term.subst, ↓reduceIte] using
    (FOL.Derivation.axiom (Axiom.mul_zero one))

private theorem oneMul_step : FormulaProves (oneMulFormula.imp
    (FOL.substAt oneMulFormula 0 (succ x))) := by
  have step : FormulaProves (oneMulFormula.imp ((mul one (succ x)).equal (succ x))) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have hcongr : FOL.Context Peano.Axiom [oneMulFormula]
        ((add (mul one x) one).equal (add x one)) :=
      .mp (.closed (add_congruence_left (mul one x) x one)) (FOL.Context.head [] oneMulFormula)
    have hfirst : FOL.Context Peano.Axiom [oneMulFormula]
        ((mul one (succ x)).equal (add x one)) :=
      FOL.Context.eqTrans (.closed (.axiom (.mul_succ one x))) hcongr
    exact FOL.Context.eqTrans hfirst (.closed (by simpa [one] using add_one x))
  simpa only [FOL.substAt, oneMulFormula, FOL.equality_subst, mul_subst, succ_subst,
    zero_subst, x, one, Term.subst, ↓reduceIte] using step

theorem one_mul_all : FormulaProves (FOL.allAt 0 ((mul (succ zero) (.var 0)).equal (.var 0))) :=
  .mp (.mp (.axiom (.induction oneMulFormula 0)) oneMul_base) (.generalize 0 oneMul_step)

theorem one_mul (t : Peano.Term) : FormulaProves ((mul (succ zero) t).equal t) := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (FOL.LogicalAxiom.allElim ((mul (succ zero) (.var 0)).equal (.var 0)) 0 t)) one_mul_all
  simpa only [FOL.substAt, FOL.equality_subst, mul_subst, succ_subst,
    zero_subst, Term.subst, ↓reduceIte] using h
end PASoundness.PeanoArithmetic
