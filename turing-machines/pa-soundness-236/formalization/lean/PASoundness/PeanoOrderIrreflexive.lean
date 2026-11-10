import PASoundness.PeanoArithmetic
import PASoundness.FOLFreshEquality
import PASoundness.CompactArithmetic
import PASoundness.CompactLogicalTransport
import Mathlib.Tactic.FinCases

/-! Object-level arithmetic towards irreflexivity of the compact order. -/
namespace PASoundness.PeanoOrderIrreflexive
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic

/-- Substitution of equals under the successor symbol in the genuine calculus. -/
theorem succ_congr (a b : Peano.Term) :
    FormulaProves ((a.equal b).imp ((succ a).equal (succ b))) := by
  obtain ⟨x, hx⟩ := FOL.fresh_for_term a
  let φ : Peano.Formula := (succ a).equal (succ (.var x))
  have h₀ : FOL.substAt φ x a = (succ a).equal (succ a) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, succ_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte]
    rw [FOL.term_subst_fresh a x a hx]
  have h₁ : FOL.substAt φ x b = (succ a).equal (succ b) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, succ_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte]
    rw [FOL.term_subst_fresh a x b hx]
  have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.eqSubst φ x a b)
  rw [h₀, h₁] at h
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  exact .mp (.mp (.closed h) (FOL.Context.head [] (a.equal b)))
    (.closed (.logical (.eqRefl _)))

private def x : Peano.Term := .var 0
private def y : Peano.Term := .var 1
private def leftSucc : Peano.Formula := (add (succ y) x).equal (succ (add y x))

private theorem leftSucc_base : FormulaProves (FOL.substAt leftSucc 0 zero) := by
  have h₁ := FOL.Derivation.axiom (Peano.Axiom.add_zero (succ y))
  have h₂ := FOL.Derivation.axiom (Peano.Axiom.add_zero y)
  have h₃ := FOL.Derivation.mp (succ_congr (add y zero) y) h₂
  have h := FOL.Derivation.eqTrans h₁ (FOL.Derivation.eqSymm h₃)
  simpa only [FOL.substAt, leftSucc, FOL.equality_subst, succ_subst,
    add_subst, zero_subst, x, y, FirstOrder.Language.Term.subst,
    if_neg (by decide : (1:Nat) ≠ 0), ↓reduceIte] using h

private theorem leftSucc_step : FormulaProves
    (leftSucc.imp (FOL.substAt leftSucc 0 (succ x))) := by
  have h₁ := FOL.Derivation.axiom (Peano.Axiom.add_succ (succ y) x)
  have h₂ := FOL.Derivation.axiom (Peano.Axiom.add_succ y x)
  have h₃ := FOL.Derivation.mp (succ_congr (add y (succ x)) (succ (add y x))) h₂
  have step : FormulaProves
      (leftSucc.imp ((add (succ y) (succ x)).equal (succ (add y (succ x))))) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have h := FOL.Context.mp (.closed (succ_congr (add (succ y) x) (succ (add y x))))
      (FOL.Context.head [] leftSucc)
    exact FOL.Context.eqTrans (FOL.Context.eqTrans (.closed h₁) h)
      (FOL.Context.eqSymm (.closed h₃))
  simpa only [FOL.substAt, leftSucc, FOL.equality_subst, succ_subst,
    add_subst, x, y, FirstOrder.Language.Term.subst,
    if_neg (by decide : (1:Nat) ≠ 0), ↓reduceIte] using step

/-- PA proves the left-successor addition identity, with a free parameter. -/
theorem left_succ_add_all : FormulaProves (FOL.allAt 0 leftSucc) :=
  .mp (.mp (.axiom (.induction leftSucc 0)) leftSucc_base) (.generalize 0 leftSucc_step)

private theorem left_succ_add_inst (t : Peano.Term) :
    FormulaProves ((add (succ y) t).equal (succ (add y t))) := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim leftSucc 0 t)) left_succ_add_all
  simpa only [FOL.substAt, leftSucc, FOL.equality_subst, add_subst, succ_subst,
    x, y, FirstOrder.Language.Term.subst, if_neg (by decide : (1:Nat) ≠ 0),
    ↓reduceIte] using h

private def z : Peano.Term := .var 2
private def noGrowth : Peano.Formula := ((add y (succ z)).equal y).not

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

private theorem noGrowth_base : FormulaProves (FOL.substAt noGrowth 1 zero) := by
  have h : FormulaProves (((add zero (succ z)).equal zero).not) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have e : FOL.Context Peano.Axiom [((add zero (succ z)).equal zero)]
        ((succ z).equal zero) :=
      FOL.Context.eqTrans (.closed (FOL.Derivation.eqSymm (zero_add (succ z))))
        (FOL.Context.head [] ((add zero (succ z)).equal zero))
    exact .mp (.closed (.axiom (.succ_ne_zero z))) e
  simpa [FOL.substAt, noGrowth, subst_not, FOL.equality_subst, add_subst, succ_subst,
    zero_subst, y, z, FirstOrder.Language.Term.subst] using h

private theorem noGrowth_step : FormulaProves
    (noGrowth.imp (FOL.substAt noGrowth 1 (succ y))) := by
  have h : FormulaProves (noGrowth.imp (((add (succ y) (succ z)).equal (succ y)).not)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have e : FOL.Context Peano.Axiom
        [((add (succ y) (succ z)).equal (succ y)), noGrowth]
        ((succ (add y (succ z))).equal (succ y)) :=
      FOL.Context.eqTrans (.closed (FOL.Derivation.eqSymm (left_succ_add_inst (succ z))))
        (FOL.Context.head _ _)
    have e' : FOL.Context Peano.Axiom
        [((add (succ y) (succ z)).equal (succ y)), noGrowth]
        ((add y (succ z)).equal y) :=
      .mp (.closed (.axiom (.succ_injective (add y (succ z)) y))) e
    exact .mp (FOL.Context.under (FOL.Context.head [] noGrowth) _) e'
  simpa [FOL.substAt, noGrowth, subst_not, FOL.equality_subst, add_subst, succ_subst,
    y, z, FirstOrder.Language.Term.subst] using h

/-- Parameterized PA induction proves that adding a positive amount is never
equal to the starting term, for the displayed two free arithmetic variables. -/
theorem no_growth_all : FormulaProves (FOL.allAt 1 noGrowth) :=
  .mp (.mp (.axiom (.induction noGrowth 1)) noGrowth_base) (.generalize 1 noGrowth_step)

/-- The self-instantiated strict order formula at variable 1 is refutable
in genuine PA. -/
theorem less_self_var : FormulaProves (CompactArithmetic.less y y).not := by
  have hg : FormulaProves noGrowth := by
    have h := FOL.Derivation.mp
      (FOL.Derivation.logical (Axiom := Peano.Axiom)
        (.allElim noGrowth 1 (.var 1))) no_growth_all
    simpa only [SyntaxTransport.substAt_self] using h
  have hall : FormulaProves (FOL.allAt 2 noGrowth) := .generalize 2 hg
  have hn : FormulaProves ((FOL.allAt 2 noGrowth).not.not) :=
    .mp (FOL.Derivation.doubleNegIntro _) hall
  have he : CompactArithmetic.less y y =
      CompactArithmetic.exAt 2 ((add y (succ z)).equal y) := by
    simp [CompactArithmetic.less, CompactArithmetic.lessTemplate, CompactArithmetic.exAt,
      CompactArithmetic.v, FOL.allAt, y, z, Peano.add, Peano.succ,
      FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
      FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.relabelAux]
    constructor
    · congr 1
      funext i
      fin_cases i
      · rfl
      · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
        congr 1
        funext j
        fin_cases j
        rfl
    · rfl
  rw [he]
  exact hn

private theorem less_var_subst (t : Peano.Term) :
    (CompactArithmetic.less y y).subst (fun a => if a = 1 then t else .var a) =
      CompactArithmetic.less t t := by
  unfold CompactArithmetic.less
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext a
  by_cases ha : a = 0
  · subst a; simp [y, FirstOrder.Language.Term.subst]
  · by_cases hb : a = 1
    · subst a; simp [y, FirstOrder.Language.Term.subst]
    · simp [ha, hb, zero_subst]

/-- The exact strict-order syntax used in the compact arithmetic
interpretation is irreflexive for every PA term. This is an object-level
derivation, independent of standard-model soundness. -/
theorem less_self (t : Peano.Term) : FormulaProves (CompactArithmetic.less t t).not := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (.allElim (CompactArithmetic.less y y).not 1 t))
    (.generalize 1 less_self_var)
  simpa only [FOL.substAt, subst_not, less_var_subst] using h

/-- The translated compact bottom is refutable once the remaining exact
object-level bit-position implication is provided at its own free variable.
This is a reduction, not a proof of that implication. -/
theorem translated_bottom_of_bit_position
    (hposition : FormulaProves
      ((CompactArithmetic.bitFormula (.var 0) (.var 0)).imp
        (CompactArithmetic.less (.var 0) (.var 0)))) :
    FormulaProves (CompactLogicalTransport.interpreted 1).not := by
  have h := FOL.Derivation.mp (FOL.Derivation.contrapose hposition) (less_self (.var 0))
  have hd : CompactMatrix.decode 1 = .member 0 0 := CompactSemantics.decode_member 0 0
  simpa only [CompactLogicalTransport.interpreted, hd, CompactArithmetic.translate,
    CompactArithmetic.v] using h

end PASoundness.PeanoOrderIrreflexive
