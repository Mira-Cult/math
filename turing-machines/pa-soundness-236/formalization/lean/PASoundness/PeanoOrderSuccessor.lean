import PASoundness.PeanoAdditionAssociative

/-! Successor invariance of the literal compact strict order, inside PA. -/
namespace PASoundness.PeanoOrderSuccessor
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoAdditionAssociative

private theorem less_before : CompactArithmetic.less (.var 0) (.var 1) =
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

private theorem less_after : CompactArithmetic.less (succ (.var 0)) (succ (.var 1)) =
    CompactArithmetic.exAt 5
      ((add (succ (.var 0)) (succ (.var 5))).equal (succ (.var 1))) := by
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
    fin_cases i <;> dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
    all_goals
      congr 1
      funext j
      fin_cases j
      rfl
  · rfl

private def beforeRow : Peano.Formula :=
  (add (.var 0) (succ (.var 5))).equal (.var 1)
private def afterRow : Peano.Formula :=
  (add (succ (.var 0)) (succ (.var 5))).equal (succ (.var 1))

private theorem row_forward : FormulaProves (beforeRow.imp afterRow) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have h : FOL.Context Peano.Axiom [beforeRow]
      ((succ (add (.var 0) (succ (.var 5)))).equal (succ (.var 1))) :=
    .mp (.closed (PeanoOrderIrreflexive.succ_congr _ _)) (FOL.Context.head [] beforeRow)
  exact FOL.Context.eqTrans (.closed (add_succ_left (.var 0) (succ (.var 5)))) h

private theorem row_backward : FormulaProves (afterRow.imp beforeRow) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have h : FOL.Context Peano.Axiom [afterRow]
      ((succ (add (.var 0) (succ (.var 5)))).equal (succ (.var 1))) :=
    FOL.Context.eqTrans
      (.closed (FOL.Derivation.eqSymm (add_succ_left (.var 0) (succ (.var 5)))))
      (FOL.Context.head [] afterRow)
  exact .mp (.closed (.axiom (.succ_injective (add (.var 0) (succ (.var 5))) (.var 1)))) h

private theorem lift_rows {φ ψ : Peano.Formula}
    (h : FormulaProves (φ.imp ψ)) (hf : 5 ∉ (FOL.existsAt 5 ψ).freeVarFinset) :
    FormulaProves ((FOL.existsAt 5 φ).imp (FOL.existsAt 5 ψ)) := by
  have introψ : FormulaProves (ψ.imp (FOL.existsAt 5 ψ)) := by
    simpa only [SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) ψ 5 (.var 5))
  exact PeanoBitPositionReduction.exists_elim 5 hf (FOL.Derivation.compose h introψ)

theorem less_succ_forward_vars :
    FormulaProves ((CompactArithmetic.less (.var 0) (.var 1)).imp
      (CompactArithmetic.less (succ (.var 0)) (succ (.var 1)))) := by
  have hf : 5 ∉ (FOL.existsAt 5 afterRow).freeVarFinset := by decide
  have h := lift_rows row_forward hf
  simpa only [less_before, less_after, CompactArithmetic.exAt, FOL.existsAt, beforeRow, afterRow] using h

theorem less_succ_backward_vars :
    FormulaProves ((CompactArithmetic.less (succ (.var 0)) (succ (.var 1))).imp
      (CompactArithmetic.less (.var 0) (.var 1))) := by
  have hf : 5 ∉ (FOL.existsAt 5 beforeRow).freeVarFinset := by decide
  have h := lift_rows row_backward hf
  simpa only [less_before, less_after, CompactArithmetic.exAt, FOL.existsAt, beforeRow, afterRow] using h

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private def succEquivalent (a b : Peano.Term) : Prop :=
  FOL.Derivation.Equivalent Peano.Axiom (CompactArithmetic.less a b)
    (CompactArithmetic.less (succ a) (succ b))

private theorem specialize (a b : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : succEquivalent a b) : succEquivalent
      (a.subst (fun y => if y = name then t else .var y))
      (b.subst (fun y => if y = name then t else .var y)) := by
  constructor
  · have h₁ := FOL.Derivation.mp
      (FOL.Derivation.logical (Axiom := Peano.Axiom)
        (.allElim ((CompactArithmetic.less a b).imp
          (CompactArithmetic.less (succ a) (succ b))) name t)) (.generalize name h.1)
    simpa only [FOL.substAt, subst_imp, CompactArithmetic.less_subst, succ_subst] using h₁
  · have h₁ := FOL.Derivation.mp
      (FOL.Derivation.logical (Axiom := Peano.Axiom)
        (.allElim ((CompactArithmetic.less (succ a) (succ b)).imp
          (CompactArithmetic.less a b)) name t)) (.generalize name h.2)
    simpa only [FOL.substAt, subst_imp, CompactArithmetic.less_subst, succ_subst] using h₁

/-- For arbitrary terms, PA derives both directions of `a < b` iff
`S a < S b` for the exact compact order. This is interderivability in the
specified Hilbert calculus, not a semantic equivalence argument. -/
theorem less_succ_iff (a b : Peano.Term) :
    FOL.Derivation.Equivalent Peano.Axiom (CompactArithmetic.less a b)
      (CompactArithmetic.less (succ a) (succ b)) := by
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
  have h0 : succEquivalent (.var 0) (.var 1) := ⟨less_succ_forward_vars, less_succ_backward_vars⟩
  have h1 := specialize _ _ 0 (.var m) h0
  have h1' : succEquivalent (.var m) (.var 1) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ 1 (.var (m+1)) h1'
  have h2' : succEquivalent (.var m) (.var (m+1)) := by
    simpa [FirstOrder.Language.Term.subst, show m ≠ 1 by omega] using h2
  have h3 := specialize _ _ m a h2'
  have h3' : succEquivalent a (.var (m+1)) := by
    simpa [FirstOrder.Language.Term.subst, show m+1 ≠ m by omega] using h3
  have h4 := specialize _ _ (m+1) b h3'
  simpa [succEquivalent, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh a (m+1) b fa] using h4

end PASoundness.PeanoOrderSuccessor
