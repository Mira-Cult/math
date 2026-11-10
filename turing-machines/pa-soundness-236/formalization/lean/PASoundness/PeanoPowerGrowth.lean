import PASoundness.PeanoPowerZero
import PASoundness.PeanoPowerPredecessor

/-! The beta-coded power growth obligation in the genuine PA calculus. -/
namespace PASoundness.PeanoPowerGrowth
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private def growthBody : Peano.Formula :=
  (pow2 (.var 0) (.var 1)).imp (less (.var 0) (.var 1))

private def growthAll : Peano.Formula := FOL.allAt 1 growthBody

private def predecessorRow : Peano.Formula :=
  (pow2 (.var 0) (.var 5)) ⊓
    ((.var 1 : Peano.Term).equal (add (.var 5) (.var 5)))

private def nextGrowth : Peano.Formula := less (succ (.var 0)) (.var 1)

private theorem doubling_step_selected : FormulaProves
    ((less (.var 0) (.var 5)).imp (less (succ (.var 0)) (add (.var 5) (.var 5)))) := by
  let φ : Peano.Formula :=
    (less (.var 1) (.var 2)).imp (less (succ (.var 1)) (add (.var 2) (.var 2)))
  have h₀ : FormulaProves φ := PeanoPowerGrowthStep.doubling_growth_step
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim φ 1 (.var 0))) (.generalize 1 h₀)
  have h₁' : FormulaProves
      ((less (.var 0) (.var 2)).imp (less (succ (.var 0)) (add (.var 2) (.var 2)))) := by
    simpa [FOL.substAt, φ, subst_imp, less_subst, succ_subst, add_subst,
      FirstOrder.Language.Term.subst] using h₁
  let ψ : Peano.Formula :=
    (less (.var 0) (.var 2)).imp (less (succ (.var 0)) (add (.var 2) (.var 2)))
  have h₂ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim ψ 2 (.var 5))) (.generalize 2 h₁')
  simpa [FOL.substAt, ψ, subst_imp, less_subst, succ_subst, add_subst,
    FirstOrder.Language.Term.subst] using h₂

/-- In the actual Hilbert calculus, a predecessor power satisfying the
inductive hypothesis yields the successor-index growth inequality. -/
private theorem row_growth : FormulaProves (predecessorRow.imp (growthAll.imp nextGrowth)) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hr : FOL.Context Peano.Axiom [growthAll, predecessorRow] predecessorRow :=
    FOL.Context.under (FOL.Context.head [] predecessorRow) growthAll
  have hg : FOL.Context Peano.Axiom [growthAll, predecessorRow] growthAll := FOL.Context.head _ _
  have hpow : FOL.Context Peano.Axiom [growthAll, predecessorRow] (pow2 (.var 0) (.var 5)) :=
    FOL.Context.conjunctionLeft hr
  have heq : FOL.Context Peano.Axiom [growthAll, predecessorRow]
      ((.var 1 : Peano.Term).equal (add (.var 5) (.var 5))) := FOL.Context.conjunctionRight hr
  have hinst := FOL.Context.allElim hg (.var 5)
  have hinst' : FOL.Context Peano.Axiom [growthAll, predecessorRow]
      ((pow2 (.var 0) (.var 5)).imp (less (.var 0) (.var 5))) := by
    simpa [FOL.substAt, growthBody, subst_imp, pow2_subst, less_subst,
      FirstOrder.Language.Term.subst] using hinst
  have hlt : FOL.Context Peano.Axiom [growthAll, predecessorRow]
      (less (succ (.var 0)) (add (.var 5) (.var 5))) :=
    .mp (.closed doubling_step_selected) (.mp hinst' hpow)
  exact .mp (.mp (.closed (PeanoMultiplyQuotientStep.less_right_congr (succ (.var 0))
    (add (.var 5) (.var 5)) (.var 1))) (FOL.Context.eqSymm heq)) hlt

private theorem growth_base_open : FormulaProves
    (FOL.allAt 1 ((pow2 zero (.var 1)).imp (less zero (.var 1)))) :=
  .generalize 1 (PeanoPowerZero.power_zero_growth (.var 1))

private theorem growth_step_open : FormulaProves
    (growthAll.imp (FOL.allAt 1
      ((pow2 (succ (.var 0)) (.var 1)).imp nextGrowth))) := by
  have hfresh : 5 ∉ (growthAll.imp nextGrowth).freeVarFinset := by decide
  have hprev := PeanoBitPositionReduction.exists_elim 5 hfresh row_growth
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.generalize 1
  · intro ψ hψ
    have he : ψ = growthAll := by simpa only [List.mem_singleton] using hψ
    subst ψ
    simp [growthAll, SyntaxTransport.allAt_freeVars]
  · apply FOL.Context.deduction
    have hend : FOL.Context Peano.Axiom [pow2 (succ (.var 0)) (.var 1), growthAll]
        (pow2 (succ (.var 0)) (.var 1)) := FOL.Context.head _ _
    have hind : FOL.Context Peano.Axiom [pow2 (succ (.var 0)) (.var 1), growthAll] growthAll :=
      FOL.Context.under (FOL.Context.head [] growthAll) _
    have hprior : FOL.Context Peano.Axiom [pow2 (succ (.var 0)) (.var 1), growthAll]
        (FOL.existsAt 5 predecessorRow) :=
      .mp (.closed PeanoPowerPredecessor.power_successor_predecessor) hend
    exact .mp (.mp (.closed hprev) hprior) hind

private theorem growth_base_syntax :
    FOL.substAt growthAll 0 zero =
      FOL.allAt 1 ((pow2 zero (.var 1)).imp (less zero (.var 1))) := by
  simp [FOL.substAt, growthAll, growthBody, FOL.allAt, pow2, pow2Template,
    beta, betaTemplate, less, lessTemplate, modulus, exAt, v, Peano.add, Peano.mul, Peano.succ,
    Peano.zero, FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux, Min.min]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])
  all_goals try simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
  all_goals try
    (congr 1; funext i; fin_cases i; congr 1; funext j; fin_cases j <;>
      dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst] <;>
      first | rfl | (congr 1; funext k; fin_cases k; rfl))
  all_goals try (congr 1; funext i; exact Fin.elim0 i)
  all_goals
    congr 1
    funext i
    fin_cases i
    congr 1
    funext j
    fin_cases j
    · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
      congr 1
      funext k
      fin_cases k
      simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
      all_goals
        congr 1
        funext z
        exact Fin.elim0 z
    · simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]

private theorem growth_step_syntax :
    FOL.substAt growthAll 0 (succ (.var 0)) =
      FOL.allAt 1 ((pow2 (succ (.var 0)) (.var 1)).imp (less (succ (.var 0)) (.var 1))) := by
  simp [FOL.substAt, growthAll, growthBody, FOL.allAt, pow2, pow2Template,
    beta, betaTemplate, less, lessTemplate, modulus, exAt, v, Peano.add, Peano.mul, Peano.succ,
    Peano.zero, FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux, Min.min]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])
  all_goals try simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
  all_goals try
    (congr 1; funext i; fin_cases i; congr 1; funext j; fin_cases j <;>
      dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst] <;>
      first | rfl | (congr 1; funext k; fin_cases k; rfl))
  all_goals try (congr 1; funext i; exact Fin.elim0 i)
  all_goals
    congr 1
    funext i
    fin_cases i
    congr 1
    funext j
    fin_cases j
    · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
      congr 1
      funext k
      fin_cases k
      simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
      all_goals
        congr 1
        funext z
        exact Fin.elim0 z
    · simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]

/-- PA derives the complete growth implication for the exact beta-coded
power formula on its two displayed free variables. -/
theorem power_growth_vars : FormulaProves
    ((pow2 (.var 0) (.var 1)).imp (less (.var 0) (.var 1))) := by
  have hbase : FormulaProves (FOL.substAt growthAll 0 zero) := by
    rw [growth_base_syntax]
    exact growth_base_open
  have hstep : FormulaProves (growthAll.imp (FOL.substAt growthAll 0 (succ (.var 0)))) := by
    rw [growth_step_syntax]
    exact growth_step_open
  have hall : FormulaProves (FOL.allAt 0 growthAll) :=
    .mp (.mp (.axiom (.induction growthAll 0)) hbase) (.generalize 0 hstep)
  have h₀ : FormulaProves growthAll := .mp (FOL.Derivation.allSelf growthAll 0) hall
  exact .mp (FOL.Derivation.allSelf growthBody 1) h₀

private def growthRelation (n p : Peano.Term) : Peano.Formula :=
  (pow2 n p).imp (less n p)

private theorem specialize (n p : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (growthRelation n p)) : FormulaProves (growthRelation
      (n.subst (fun y => if y = name then t else .var y))
      (p.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (growthRelation n p) name t))
    (.generalize name h)
  simpa only [FOL.substAt, growthRelation, subst_imp, pow2_subst, less_subst] using h₁

/-- For arbitrary arithmetic terms, PA proves that any literal beta-coded
power trace at index n has endpoint strictly greater than n. -/
theorem power_growth (n p : Peano.Term) :
    FormulaProves ((pow2 n p).imp (less n p)) := by
  let support := n.varFinset ∪ p.varFinset
  let k := support.sup id + 2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have fresh (j : Nat) (hj : k ≤ j) : j ∉ support := by
    intro h
    have hle : j ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [k] at hj
    omega
  have hn : k+1 ∉ n.varFinset := by
    intro h
    apply fresh (k+1) (by omega)
    simp [support, h]
  have h1 := specialize _ _ 0 (.var k) power_growth_vars
  have h1' : FormulaProves (growthRelation (.var k) (.var 1)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ 1 (.var (k+1)) h1'
  have h2' : FormulaProves (growthRelation (.var k) (.var (k+1))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 1 by omega] using h2
  have h3 := specialize _ _ k n h2'
  have h3' : FormulaProves (growthRelation n (.var (k+1))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega] using h3
  have h4 := specialize _ _ (k+1) p h3'
  simpa [growthRelation, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh n (k+1) p hn] using h4

/-- The formerly open translated-bottom obligation is discharged by the
constructed PA proof of the literal power-growth implication. -/
theorem translated_bottom : FormulaProves (CompactLogicalTransport.interpreted 1).not :=
  PeanoAdditionAssociative.translated_bottom_of_power_growth (power_growth (.var 1) (.var 2))

/-- The existing finite compact-to-PA proof transport now needs only the
explicit family of object-level finite-comprehension derivations. That
comprehension premise and the reverse proof transport remain open. -/
theorem proofToPA_of_comprehension
    (hcomprehension : ∀ a b c, c ≠ a → c ≠ b →
      FormulaProves (CompactLogicalTransport.comprehensionFormula a b c))
    {f : Nat} (d : CompactProof.KDerivation f) : Peano.Proves (toPA f) :=
  CompactLogicalTransport.proofToPA_of_arithmetic_obligations translated_bottom hcomprehension d

end PASoundness.PeanoPowerGrowth
