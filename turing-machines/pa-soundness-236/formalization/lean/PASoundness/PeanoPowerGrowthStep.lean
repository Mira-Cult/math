import PASoundness.PeanoAdditionAssociative

/-! A genuine PA step toward growth of the beta-coded power trace. -/
namespace PASoundness.PeanoPowerGrowthStep
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoAdditionAssociative

/-- From `x + S d = p`, PA derives an explicit witness equation showing
`S x` is strictly below `p+p`. No semantic arithmetic is used. -/
theorem doubling_witness_equation (x p d : Peano.Term) :
    FormulaProves (((add x (succ d)).equal p).imp
      ((add p p).equal (add (succ x) (succ (add (add d x) d))))) := by
  let input : Peano.Formula := (add x (succ d)).equal p
  let w : Peano.Term := add (add d x) d
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hx : FOL.Context Peano.Axiom [input] ((add x (succ d)).equal p) :=
    FOL.Context.head [] input
  have h₁ : FOL.Context Peano.Axiom [input]
      ((add p p).equal (add (add x (succ d)) p)) :=
    .mp (.closed (add_left_congr p p (add x (succ d)))) (FOL.Context.eqSymm hx)
  have h₂ : FOL.Context Peano.Axiom [input]
      ((add p p).equal (add x (add (succ d) p))) :=
    FOL.Context.eqTrans h₁ (.closed (add_assoc x (succ d) p))
  have h₃ : FOL.Context Peano.Axiom [input]
      ((add p p).equal (add x (succ (add d p)))) :=
    FOL.Context.eqTrans h₂ (.mp (.closed (add_right_congr x _ _))
      (.closed (add_succ_left d p)))
  have h₄ : FOL.Context Peano.Axiom [input]
      ((add d p).equal (add d (add x (succ d)))) :=
    .mp (.closed (add_right_congr d p (add x (succ d)))) (FOL.Context.eqSymm hx)
  have h₅ : FOL.Context Peano.Axiom [input] ((add d p).equal (succ w)) :=
    FOL.Context.eqTrans (FOL.Context.eqTrans h₄ (.closed (FOL.Derivation.eqSymm
      (add_assoc d x (succ d))))) (.closed (.axiom (.add_succ (add d x) d)))
  have h₆ : FOL.Context Peano.Axiom [input]
      ((add p p).equal (add x (succ (succ w)))) :=
    FOL.Context.eqTrans h₃ (.mp (.closed (add_right_congr x _ _))
      (.mp (.closed (PeanoOrderIrreflexive.succ_congr _ _)) h₅))
  have h₇ : FormulaProves ((add x (succ (succ w))).equal (add (succ x) (succ w))) :=
    FOL.Derivation.eqTrans (.axiom (.add_succ x (succ w)))
      (FOL.Derivation.eqSymm (add_succ_left x (succ w)))
  exact FOL.Context.eqTrans h₆ (.closed h₇)

private theorem less_before :
    CompactArithmetic.less (.var 1) (.var 2) =
      CompactArithmetic.exAt 5 ((add (.var 1) (succ (.var 5))).equal (.var 2)) := by
  simp [CompactArithmetic.less, CompactArithmetic.lessTemplate, CompactArithmetic.exAt,
    CompactArithmetic.v, FOL.allAt, Peano.add, Peano.succ,
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

private theorem less_after :
    CompactArithmetic.less (succ (.var 1)) (add (.var 2) (.var 2)) =
      CompactArithmetic.exAt 5
        ((add (succ (.var 1)) (succ (.var 5))).equal (add (.var 2) (.var 2))) := by
  simp [CompactArithmetic.less, CompactArithmetic.lessTemplate, CompactArithmetic.exAt,
    CompactArithmetic.v, FOL.allAt, Peano.add, Peano.succ,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  constructor
  · constructor
    · congr 1
      funext i
      fin_cases i <;> dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
      all_goals
        congr 1
        funext j
        fin_cases j
        rfl
    · congr 1
      funext i
      fin_cases i <;> rfl
  · rfl

/-- The exact compact arithmetic order is preserved by one doubling step:
PA derives `x < p → S x < p+p`, with the two displayed free variables.
The proof is syntactic and has no power-trace or semantic assumptions. -/
theorem doubling_growth_step :
    FormulaProves ((CompactArithmetic.less (.var 1) (.var 2)).imp
      (CompactArithmetic.less (succ (.var 1)) (add (.var 2) (.var 2)))) := by
  let x : Peano.Term := .var 1
  let p : Peano.Term := .var 2
  let d : Peano.Term := .var 5
  let input : Peano.Formula := (add x (succ d)).equal p
  let output : Peano.Formula := (add (succ x) (succ d)).equal (add p p)
  let result : Peano.Formula := CompactArithmetic.less (succ x) (add p p)
  let witness : Peano.Term := add (add d x) d
  have hw : FormulaProves (input.imp result) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have heq : FOL.Context Peano.Axiom [input]
        ((add (succ x) (succ witness)).equal (add p p)) :=
      FOL.Context.eqSymm (.mp (.closed (doubling_witness_equation x p d))
        (FOL.Context.head [] input))
    have hsubst : FOL.substAt output 5 witness =
        (add (succ x) (succ witness)).equal (add p p) := by
      simp [FOL.substAt, output, x, p, d, FOL.equality_subst, add_subst, succ_subst,
        FirstOrder.Language.Term.subst]
    have hex : FOL.Context Peano.Axiom [input] (FOL.existsAt 5 output) := by
      apply FOL.Context.mp (.closed (FOL.Derivation.existsIntro output 5 witness))
      rw [hsubst]
      exact heq
    change FOL.Context Peano.Axiom [input] (CompactArithmetic.less (succ (.var 1))
      (add (.var 2) (.var 2)))
    rw [less_after]
    exact hex
  have hfresh : 5 ∉ result.freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 5 hfresh hw
  simpa only [x, p, d, input, result, less_before,
    CompactArithmetic.exAt, FOL.existsAt] using h

private theorem less_zero_one_eq :
    CompactArithmetic.less zero (succ zero) =
      CompactArithmetic.exAt 5 ((add zero (succ (.var 5))).equal (succ zero)) := by
  simp [CompactArithmetic.less, CompactArithmetic.lessTemplate, CompactArithmetic.exAt,
    CompactArithmetic.v, FOL.allAt, Peano.add, Peano.succ, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]

  constructor
  · constructor
    · congr 1
      funext i
      fin_cases i
      · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
        congr 1
        funext j
        exact Fin.elim0 j
      · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
        congr 1
        funext j
        fin_cases j
        rfl
    · congr 1
      funext i
      fin_cases i
      congr 1
      funext j
      exact Fin.elim0 j
  · rfl

/-- Base arithmetic fact for the power-growth induction, in the exact compact
order syntax. -/
theorem zero_less_one : FormulaProves (CompactArithmetic.less zero (succ zero)) := by
  rw [less_zero_one_eq]
  let body : Peano.Formula := (add zero (succ (.var 5))).equal (succ zero)
  have he : FOL.substAt body 5 zero = (add zero (succ zero)).equal (succ zero) := by
    simp [FOL.substAt, body, FOL.equality_subst, add_subst, succ_subst,
      zero_subst, FirstOrder.Language.Term.subst]
  have h := FOL.Derivation.existsIntro (A := Peano.Axiom) body 5 zero
  rw [he] at h
  exact .mp h (zero_add (succ zero))

end PASoundness.PeanoPowerGrowthStep
