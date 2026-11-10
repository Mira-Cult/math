import PASoundness.PeanoAdditionAssociative
import PASoundness.PeanoOrderAsymmetry

/-! Transitivity of the literal compact arithmetic order inside PA. -/
namespace PASoundness.PeanoOrderTransitive
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoAdditionAssociative

private theorem less01 : CompactArithmetic.less (.var 0) (.var 1) =
    CompactArithmetic.exAt 5 ((add (.var 0) (succ (.var 5))).equal (.var 1)) := by
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

private theorem less12 : CompactArithmetic.less (.var 1) (.var 2) =
    CompactArithmetic.exAt 6 ((add (.var 1) (succ (.var 6))).equal (.var 2)) := by
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

private theorem less02 : CompactArithmetic.less (.var 0) (.var 2) =
    CompactArithmetic.exAt 7 ((add (.var 0) (succ (.var 7))).equal (.var 2)) := by
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

/-- PA derives transitivity on three fixed free variables by composing the
two actual order witnesses. -/
theorem less_transitive_vars :
    FormulaProves ((CompactArithmetic.less (.var 0) (.var 1)).imp
      ((CompactArithmetic.less (.var 1) (.var 2)).imp
        (CompactArithmetic.less (.var 0) (.var 2)))) := by
  let A : Peano.Term := .var 0
  let B : Peano.Term := .var 1
  let C : Peano.Term := .var 2
  let D : Peano.Term := .var 5
  let E : Peano.Term := .var 6
  let first : Peano.Formula := (add A (succ D)).equal B
  let second : Peano.Formula := (add B (succ E)).equal C
  let output : Peano.Formula := (add A (succ (.var 7))).equal C
  let goal : Peano.Formula := CompactArithmetic.less A C
  let witness : Peano.Term := add D (succ E)
  have hrows : FormulaProves (second.imp (first.imp goal)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hfirst : FOL.Context Peano.Axiom [first, second] first := FOL.Context.head _ _
    have hsecond : FOL.Context Peano.Axiom [first, second] second :=
      FOL.Context.under (FOL.Context.head [] second) first
    have h₁ : FOL.Context Peano.Axiom [first, second]
        ((add (add A (succ D)) (succ E)).equal C) :=
      FOL.Context.eqTrans (.mp (.closed (add_left_congr (succ E) _ _)) hfirst) hsecond
    have h₂ : FOL.Context Peano.Axiom [first, second]
        ((add A (succ witness)).equal C) :=
      FOL.Context.eqTrans (FOL.Context.eqSymm
        (FOL.Context.eqTrans (.closed (add_assoc A (succ D) (succ E)))
          (.mp (.closed (add_right_congr A _ _)) (.closed (add_succ_left D (succ E)))))) h₁
    have hs : FOL.substAt output 7 witness = (add A (succ witness)).equal C := by
      simp [FOL.substAt, output, A, C, FOL.equality_subst, add_subst, succ_subst,
        FirstOrder.Language.Term.subst]
    have hex : FOL.Context Peano.Axiom [first, second] (FOL.existsAt 7 output) := by
      apply FOL.Context.mp (.closed (FOL.Derivation.existsIntro output 7 witness))
      rw [hs]
      exact h₂
    change FOL.Context Peano.Axiom [first, second] (CompactArithmetic.less (.var 0) (.var 2))
    rw [less02]
    exact hex
  have hfresh6 : 6 ∉ (first.imp goal).freeVarFinset := by decide
  have he6 := PeanoBitPositionReduction.exists_elim 6 hfresh6 hrows
  have hswap : FormulaProves (first.imp ((FOL.existsAt 6 second).imp goal)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    exact .mp (.mp (.closed he6) (FOL.Context.head [first] _))
      (FOL.Context.under (FOL.Context.head [] first) _)
  have hfresh5 : 5 ∉ ((FOL.existsAt 6 second).imp goal).freeVarFinset := by decide
  have he5 := PeanoBitPositionReduction.exists_elim 5 hfresh5 hswap
  simpa only [A, B, C, D, E, first, second, goal, less01, less12,
    CompactArithmetic.exAt, FOL.existsAt] using he5

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private def transitivity (a b c : Peano.Term) : Peano.Formula :=
  (CompactArithmetic.less a b).imp
    ((CompactArithmetic.less b c).imp (CompactArithmetic.less a c))

private theorem specialize (a b c : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (transitivity a b c)) : FormulaProves (transitivity
      (a.subst (fun y => if y = name then t else .var y))
      (b.subst (fun y => if y = name then t else .var y))
      (c.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (transitivity a b c) name t))
    (.generalize name h)
  simpa only [FOL.substAt, transitivity, subst_imp, CompactArithmetic.less_subst] using h₁

/-- The exact compact arithmetic strict order is transitive in PA for all
arithmetic terms, including terms with shared free variables. -/
theorem less_transitive_all (a b c : Peano.Term) :
    FormulaProves ((CompactArithmetic.less a b).imp
      ((CompactArithmetic.less b c).imp (CompactArithmetic.less a c))) := by
  let support := a.varFinset ∪ b.varFinset ∪ c.varFinset
  let m := support.sup id + 3
  have hm : 3 ≤ m := by dsimp [m]; omega
  have fresh (n : Nat) (hn : m ≤ n) : n ∉ support := by
    intro h
    have hle : n ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [m] at hn
    omega
  have fa (n : Nat) (hn : m ≤ n) : n ∉ a.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have fb (n : Nat) (hn : m ≤ n) : n ∉ b.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have h1 := specialize _ _ _ 0 (.var m) less_transitive_vars
  have h1' : FormulaProves (transitivity (.var m) (.var 1) (.var 2)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ _ 1 (.var (m+1)) h1'
  have h2' : FormulaProves (transitivity (.var m) (.var (m+1)) (.var 2)) := by
    simpa [FirstOrder.Language.Term.subst, show m ≠ 1 by omega] using h2
  have h3 := specialize _ _ _ 2 (.var (m+2)) h2'
  have h3' : FormulaProves (transitivity (.var m) (.var (m+1)) (.var (m+2))) := by
    simpa [FirstOrder.Language.Term.subst, show m ≠ 2 by omega,
      show m+1 ≠ 2 by omega] using h3
  have h4 := specialize _ _ _ m a h3'
  have h4' : FormulaProves (transitivity a (.var (m+1)) (.var (m+2))) := by
    simpa [FirstOrder.Language.Term.subst, show m+1 ≠ m by omega,
      show m+2 ≠ m by omega] using h4
  have h5 := specialize _ _ _ (m+1) b h4'
  have h5' : FormulaProves (transitivity a b (.var (m+2))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh a (m+1) b (fa _ (by omega)),
      show m+2 ≠ m+1 by omega] using h5
  have h6 := specialize _ _ _ (m+2) c h5'
  simpa [transitivity, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh a (m+2) c (fa _ (by omega)),
    FOL.term_subst_fresh b (m+2) c (fb _ (by omega))] using h6

/-- PA excludes a three-edge strict-order cycle on arbitrary terms. -/
theorem no_three_cycle (a b c : Peano.Term) :
    FormulaProves ((CompactArithmetic.less a b).imp
      ((CompactArithmetic.less b c).imp (CompactArithmetic.less c a).not)) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hab : FOL.Context Peano.Axiom [CompactArithmetic.less b c, CompactArithmetic.less a b]
      (CompactArithmetic.less a b) :=
    FOL.Context.under (FOL.Context.head [] _) _
  have hbc : FOL.Context Peano.Axiom [CompactArithmetic.less b c, CompactArithmetic.less a b]
      (CompactArithmetic.less b c) := FOL.Context.head _ _
  have hac : FOL.Context Peano.Axiom [CompactArithmetic.less b c, CompactArithmetic.less a b]
      (CompactArithmetic.less a c) := .mp (.mp (.closed (less_transitive_all a b c)) hab) hbc
  exact .mp (.closed (PeanoOrderAsymmetry.less_asymmetric_all a c)) hac

end PASoundness.PeanoOrderTransitive
