import PASoundness.PeanoAdditionCancellation

/-! Strict-order asymmetry in the genuine PA proof calculus. -/
namespace PASoundness.PeanoOrderAsymmetry
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoAdditionAssociative PeanoAdditionCancellation

/-- PA derives that adding a positive successor cannot preserve the original
term. This is an explicit finite derivation from left cancellation. -/
theorem no_positive_self_add (a d : Peano.Term) :
    FormulaProves ((add a (succ d)).equal a).not := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom [((add a (succ d)).equal a)]
      ((add a (succ d)).equal (add a zero)) :=
    FOL.Context.eqTrans (FOL.Context.head [] _)
      (.closed (FOL.Derivation.eqSymm (.axiom (.add_zero a))))
  have hf : FOL.Context Peano.Axiom [((add a (succ d)).equal a)]
      ((succ d).equal zero) := .mp (.closed (add_left_cancel a (succ d) zero)) he
  exact .mp (.closed (.axiom (.succ_ne_zero d))) hf

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

private theorem less10 : CompactArithmetic.less (.var 1) (.var 0) =
    CompactArithmetic.exAt 6 ((add (.var 1) (succ (.var 6))).equal (.var 0)) := by
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

/-- On its two free arithmetic variables, PA derives the asymmetry of the
literal compact strict-order formula. -/
theorem less_asymmetric :
    FormulaProves ((CompactArithmetic.less (.var 0) (.var 1)).imp
      (CompactArithmetic.less (.var 1) (.var 0)).not) := by
  let X : Peano.Term := .var 0
  let Y : Peano.Term := .var 1
  let D : Peano.Term := .var 5
  let E : Peano.Term := .var 6
  let first : Peano.Formula := (add X (succ D)).equal Y
  let second : Peano.Formula := (add Y (succ E)).equal X
  have hrows : FormulaProves (second.imp first.not) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hfirst : FOL.Context Peano.Axiom [first, second] first := FOL.Context.head _ _
    have hsecond : FOL.Context Peano.Axiom [first, second] second :=
      FOL.Context.under (FOL.Context.head [] second) first
    have h₁ : FOL.Context Peano.Axiom [first, second]
        ((add (add X (succ D)) (succ E)).equal X) :=
      FOL.Context.eqTrans (.mp (.closed (add_left_congr (succ E) _ _)) hfirst) hsecond
    have h₂ : FOL.Context Peano.Axiom [first, second]
        ((add X (succ (add D (succ E)))).equal X) :=
      FOL.Context.eqTrans (FOL.Context.eqSymm
        (FOL.Context.eqTrans (.closed (add_assoc X (succ D) (succ E)))
          (.mp (.closed (add_right_congr X _ _)) (.closed (add_succ_left D (succ E)))))) h₁
    exact .mp (.closed (no_positive_self_add X (add D (succ E)))) h₂
  have fresh6 : 6 ∉ first.not.freeVarFinset := by decide
  have hsecond := PeanoBitPositionReduction.exists_elim 6 fresh6 hrows
  have hfirst : FormulaProves (first.imp (FOL.existsAt 6 second).not) :=
    FOL.Derivation.compose (FOL.Derivation.doubleNegIntro first)
      (FOL.Derivation.contrapose hsecond)
  have fresh5 : 5 ∉ (FOL.existsAt 6 second).not.freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 5 fresh5 hfirst
  simpa only [X, Y, D, E, first, second, less01, less10,
    CompactArithmetic.exAt, FOL.existsAt] using h

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

private def asymmetry (a b : Peano.Term) : Peano.Formula :=
  (CompactArithmetic.less a b).imp (CompactArithmetic.less b a).not

private theorem specialize (a b : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (asymmetry a b)) :
    FormulaProves (asymmetry
      (a.subst (fun y => if y = name then t else .var y))
      (b.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (asymmetry a b) name t))
    (.generalize name h)
  simpa only [FOL.substAt, asymmetry, subst_imp, subst_not, CompactArithmetic.less_subst] using h₁

/-- Strict order is asymmetric for arbitrary arithmetic terms, including
terms sharing variables, by a capture-safe finite PA proof transformation. -/
theorem less_asymmetric_all (a b : Peano.Term) :
    FormulaProves ((CompactArithmetic.less a b).imp (CompactArithmetic.less b a).not) := by
  let support := a.varFinset ∪ b.varFinset
  let m := support.sup id + 2
  have hm : 2 ≤ m := by dsimp [m]; omega
  have fresh (n : Nat) (hn : m ≤ n) : n ∉ support := by
    intro h
    have hle : n ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [m] at hn
    omega
  have fa : m+1 ∉ a.varFinset := by
    intro h
    apply fresh (m+1) (by omega)
    simp [support, h]
  have h0 : FormulaProves (asymmetry (.var 0) (.var 1)) := less_asymmetric
  have h1 := specialize _ _ 0 (.var m) h0
  have h1' : FormulaProves (asymmetry (.var m) (.var 1)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ 1 (.var (m+1)) h1'
  have h2' : FormulaProves (asymmetry (.var m) (.var (m+1))) := by
    simpa [FirstOrder.Language.Term.subst, show m ≠ 1 by omega] using h2
  have h3 := specialize _ _ m a h2'
  have h3' : FormulaProves (asymmetry a (.var (m+1))) := by
    simpa [FirstOrder.Language.Term.subst, show m+1 ≠ m by omega] using h3
  have h4 := specialize _ _ (m+1) b h3'
  simpa [asymmetry, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh a (m+1) b fa] using h4

end PASoundness.PeanoOrderAsymmetry
