import PASoundness.PeanoOrderSuccessor

/-! Finite PA comparison arguments toward totality of the compact order. -/
namespace PASoundness.PeanoOrderTotality
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic

private theorem or_left {L : Language} {A : FOL.Formula L → Prop}
    {Γ : List (FOL.Formula L)} {φ ψ : FOL.Formula L} (h : FOL.Context A Γ φ) :
    FOL.Context A Γ (φ ⊔ ψ) := by
  change FOL.Context A Γ (φ.not.imp ψ)
  apply FOL.Context.deduction
  exact FOL.Context.explode ψ (.mp (FOL.Context.head Γ φ.not) (FOL.Context.under h φ.not))

private theorem or_right {L : Language} {A : FOL.Formula L → Prop}
    {Γ : List (FOL.Formula L)} {φ ψ : FOL.Formula L} (h : FOL.Context A Γ ψ) :
    FOL.Context A Γ (φ ⊔ ψ) := FOL.Context.lift h φ.not

private theorem or_elim {L : Language} {A : FOL.Formula L → Prop}
    {Γ : List (FOL.Formula L)} {φ ψ χ : FOL.Formula L}
    (h : FOL.Context A Γ (φ ⊔ ψ)) (hφ : FOL.Context A Γ (φ.imp χ))
    (hψ : FOL.Context A Γ (ψ.imp χ)) : FOL.Context A Γ χ := by
  apply FOL.Context.dne
  apply FOL.Context.deduction
  have hnφ : FOL.Context A (χ.not :: Γ) φ.not :=
    .mp (FOL.Context.under (FOL.Context.contrapose hφ) χ.not) (FOL.Context.head Γ χ.not)
  have hψ' : FOL.Context A (χ.not :: Γ) ψ :=
    .mp (FOL.Context.under h χ.not) hnφ
  exact .mp (FOL.Context.head Γ χ.not) (.mp (FOL.Context.under hψ χ.not) hψ')

/-- Explicit syntactic trichotomy: equality, left strict, or right strict. -/
def trichotomy (a b : Peano.Term) : Peano.Formula :=
  ((a.equal b) ⊔ CompactArithmetic.less a b) ⊔ CompactArithmetic.less b a

/-- PA derives the successor-to-successor trichotomy step for arbitrary
arithmetic terms. No totality or semantic premise is used. -/
theorem trichotomy_succ_step (a b : Peano.Term) :
    FormulaProves ((trichotomy a b).imp (trichotomy (succ a) (succ b))) := by
  let E : Peano.Formula := a.equal b
  let L : Peano.Formula := CompactArithmetic.less a b
  let G : Peano.Formula := CompactArithmetic.less b a
  let T : Peano.Formula := trichotomy (succ a) (succ b)
  have he : FormulaProves (E.imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    change FOL.Context Peano.Axiom [E]
      (((succ a).equal (succ b) ⊔ CompactArithmetic.less (succ a) (succ b)) ⊔
        CompactArithmetic.less (succ b) (succ a))
    apply or_left
    apply or_left
    exact .mp (.closed (PeanoOrderIrreflexive.succ_congr a b)) (FOL.Context.head [] E)
  have hl : FormulaProves (L.imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    change FOL.Context Peano.Axiom [L]
      (((succ a).equal (succ b) ⊔ CompactArithmetic.less (succ a) (succ b)) ⊔
        CompactArithmetic.less (succ b) (succ a))
    apply or_left
    apply or_right
    exact .mp (.closed (PeanoOrderSuccessor.less_succ_iff a b).1) (FOL.Context.head [] L)
  have hg : FormulaProves (G.imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    change FOL.Context Peano.Axiom [G]
      (((succ a).equal (succ b) ⊔ CompactArithmetic.less (succ a) (succ b)) ⊔
        CompactArithmetic.less (succ b) (succ a))
    apply or_right
    exact .mp (.closed (PeanoOrderSuccessor.less_succ_iff b a).1) (FOL.Context.head [] G)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hinner : FOL.Context Peano.Axiom [trichotomy a b] ((E ⊔ L).imp T) := by
    apply FOL.Context.deduction
    exact or_elim (FOL.Context.head _ (E ⊔ L)) (.closed he) (.closed hl)
  exact or_elim (FOL.Context.head [] (trichotomy a b)) hinner (.closed hg)

private theorem zero_less_succ_var_eq :
    CompactArithmetic.less zero (succ (.var 1)) =
      CompactArithmetic.exAt 5 ((add zero (succ (.var 5))).equal (succ (.var 1))) := by
  simp [CompactArithmetic.less, CompactArithmetic.lessTemplate, CompactArithmetic.exAt,
    CompactArithmetic.v, FOL.allAt, Peano.add, Peano.succ, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  constructor
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
  · rfl

private theorem zero_less_succ_var :
    FormulaProves (CompactArithmetic.less zero (succ (.var 1))) := by
  rw [zero_less_succ_var_eq]
  let body : Peano.Formula := (add zero (succ (.var 5))).equal (succ (.var 1))
  have he : FOL.substAt body 5 (.var 1) =
      (add zero (succ (.var 1))).equal (succ (.var 1)) := by
    simp [FOL.substAt, body, FOL.equality_subst, add_subst, succ_subst,
      PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst]
  have h := FOL.Derivation.existsIntro (A := Peano.Axiom) body 5 (.var 1)
  rw [he] at h
  exact .mp h (zero_add (succ (.var 1)))

/-- PA derives `0 < S t` for any arithmetic term, in the exact compact
order syntax. -/
theorem zero_less_succ (t : Peano.Term) :
    FormulaProves (CompactArithmetic.less zero (succ t)) := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (.allElim (CompactArithmetic.less zero (succ (.var 1))) 1 t))
    (.generalize 1 zero_less_succ_var)
  simpa [FOL.substAt, CompactArithmetic.less_subst, succ_subst,
    PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst] using h

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

private theorem subst_or (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊔ ψ).subst σ = (φ.subst σ) ⊔ (ψ.subst σ) := by
  change (φ.not.imp ψ).subst σ = (φ.subst σ).not.imp (ψ.subst σ)
  rw [subst_imp, subst_not]

private theorem trichotomy_subst (a b : Peano.Term) (σ : Nat → Peano.Term) :
    (trichotomy a b).subst σ = trichotomy (a.subst σ) (b.subst σ) := by
  simp only [trichotomy, subst_or, FOL.equality_subst, CompactArithmetic.less_subst]

private def zeroCase : Peano.Formula := trichotomy zero (.var 1)

private theorem zero_case_base : FormulaProves (FOL.substAt zeroCase 1 zero) := by
  have h : FormulaProves (trichotomy zero zero) := by
    apply FOL.Context.closeEmpty
    change FOL.Context Peano.Axiom []
      (((zero.equal zero) ⊔ CompactArithmetic.less zero zero) ⊔ CompactArithmetic.less zero zero)
    exact or_left (or_left (.closed (.logical (.eqRefl zero))))
  simpa [FOL.substAt, zeroCase, trichotomy_subst, PeanoArithmetic.zero_subst,
    FirstOrder.Language.Term.subst] using h

private theorem zero_case_step :
    FormulaProves (zeroCase.imp (FOL.substAt zeroCase 1 (succ (.var 1)))) := by
  have h : FormulaProves (trichotomy zero (succ (.var 1))) := by
    apply FOL.Context.closeEmpty
    change FOL.Context Peano.Axiom []
      (((zero.equal (succ (.var 1))) ⊔ CompactArithmetic.less zero (succ (.var 1))) ⊔
        CompactArithmetic.less (succ (.var 1)) zero)
    exact or_left (or_right (.closed (zero_less_succ (.var 1))))
  have hw := FOL.Derivation.weakening h zeroCase
  simpa [FOL.substAt, zeroCase, trichotomy_subst, PeanoArithmetic.zero_subst,
    FirstOrder.Language.Term.subst] using hw

/-- Zero compares with every number, as an actual PA induction theorem. -/
theorem zero_trichotomy : FormulaProves (FOL.allAt 1 zeroCase) :=
  .mp (.mp (.axiom (.induction zeroCase 1)) zero_case_base) (.generalize 1 zero_case_step)

private def allCompare : Peano.Formula := FOL.allAt 1 (trichotomy (.var 0) (.var 1))

private theorem allCompare_base_syntax :
    FOL.substAt allCompare 0 zero = FOL.allAt 1 zeroCase := by
  simp [FOL.substAt, allCompare, zeroCase, trichotomy, CompactArithmetic.less,
    CompactArithmetic.lessTemplate, CompactArithmetic.exAt, CompactArithmetic.v, FOL.allAt,
    Peano.add, Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst,
    FirstOrder.Language.Term.relabel, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.subst, FirstOrder.Language.BoundedFormula.relabel,
    FirstOrder.Language.BoundedFormula.mapTermRel, FirstOrder.Language.BoundedFormula.relabelAux,
    Max.max]
  constructor
  · constructor
    · congr 1
      funext i
      exact Fin.elim0 i
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
  · constructor
    · congr 1
      funext i
      fin_cases i
      · rfl
      · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
        congr 1
        funext j
        fin_cases j
        rfl
    · congr 1
      funext i
      exact Fin.elim0 i

private theorem allCompare_step_syntax :
    FOL.substAt allCompare 0 (succ (.var 0)) =
      FOL.allAt 1 (trichotomy (succ (.var 0)) (.var 1)) := by
  simp [FOL.substAt, allCompare, trichotomy, CompactArithmetic.less,
    CompactArithmetic.lessTemplate, CompactArithmetic.exAt, CompactArithmetic.v, FOL.allAt,
    Peano.add, Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst,
    FirstOrder.Language.Term.relabel, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.subst, FirstOrder.Language.BoundedFormula.relabel,
    FirstOrder.Language.BoundedFormula.mapTermRel, FirstOrder.Language.BoundedFormula.relabelAux,
    Max.max]
  constructor
  all_goals
    congr 1
    funext i
    fin_cases i <;>
      dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst] <;>
      first | rfl | (congr 1; funext j; fin_cases j; rfl)

private def innerCompare : Peano.Formula := trichotomy (succ (.var 0)) (.var 1)

private theorem inner_base : FormulaProves (FOL.substAt innerCompare 1 zero) := by
  have h : FormulaProves (trichotomy (succ (.var 0)) zero) := by
    apply FOL.Context.closeEmpty
    change FOL.Context Peano.Axiom []
      ((((succ (.var 0)).equal zero) ⊔ CompactArithmetic.less (succ (.var 0)) zero) ⊔
        CompactArithmetic.less zero (succ (.var 0)))
    exact or_right (.closed (zero_less_succ (.var 0)))
  simpa [FOL.substAt, innerCompare, trichotomy_subst, succ_subst,
    PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst] using h

private theorem inner_from_outer :
    FOL.Context Peano.Axiom [allCompare] (FOL.allAt 1 innerCompare) := by
  have hstep : FOL.Context Peano.Axiom [allCompare]
      (FOL.allAt 1 (innerCompare.imp (FOL.substAt innerCompare 1 (succ (.var 1))))) := by
    apply FOL.Context.generalize 1
    · intro ψ hψ
      have he : ψ = allCompare := by simpa only [List.mem_singleton] using hψ
      subst ψ
      simp [allCompare, SyntaxTransport.allAt_freeVars]
    · have hcomp : FOL.Context Peano.Axiom [allCompare] (trichotomy (.var 0) (.var 1)) := by
        apply FOL.Context.allSelf
        exact FOL.Context.head [] allCompare
      have hnext : FOL.Context Peano.Axiom [allCompare]
          (trichotomy (succ (.var 0)) (succ (.var 1))) :=
        .mp (.closed (trichotomy_succ_step (.var 0) (.var 1))) hcomp
      have hweak := FOL.Context.lift hnext innerCompare
      simpa [FOL.substAt, innerCompare, trichotomy_subst, succ_subst,
        FirstOrder.Language.Term.subst] using hweak
  exact .mp (.mp (.closed (.axiom (.induction innerCompare 1))) (.closed inner_base)) hstep

private theorem allCompare_step :
    FormulaProves (allCompare.imp (FOL.substAt allCompare 0 (succ (.var 0)))) := by
  rw [allCompare_step_syntax]
  exact FOL.Context.closeEmpty (FOL.Context.deduction inner_from_outer)

/-- PA proves trichotomy simultaneously for all values of the two free
variables, using the actual parameterized induction schema twice. -/
theorem trichotomy_vars : FormulaProves (trichotomy (.var 0) (.var 1)) := by
  have hbase : FormulaProves (FOL.substAt allCompare 0 zero) := by
    rw [allCompare_base_syntax]
    exact zero_trichotomy
  have houter : FormulaProves (FOL.allAt 0 allCompare) :=
    .mp (.mp (.axiom (.induction allCompare 0)) hbase) (.generalize 0 allCompare_step)
  have h0 : FormulaProves allCompare := FOL.Derivation.mp
    (FOL.Derivation.allSelf allCompare 0) houter
  exact FOL.Derivation.mp (FOL.Derivation.allSelf _ 1) h0

private theorem specialize (a b : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (trichotomy a b)) : FormulaProves (trichotomy
      (a.subst (fun y => if y = name then t else .var y))
      (b.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (trichotomy a b) name t))
    (.generalize name h)
  simpa only [FOL.substAt, trichotomy_subst] using h₁

/-- Arbitrary-term trichotomy in genuine first-order PA, with the exact
compact `<` relation. The proof is syntactic; the two temporary variables
are fresh from both terms, so shared free variables are permitted. -/
theorem trichotomy_all (a b : Peano.Term) : FormulaProves (trichotomy a b) := by
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
  have h1 := specialize _ _ 0 (.var m) trichotomy_vars
  have h1' : FormulaProves (trichotomy (.var m) (.var 1)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ 1 (.var (m+1)) h1'
  have h2' : FormulaProves (trichotomy (.var m) (.var (m+1))) := by
    simpa [FirstOrder.Language.Term.subst, show m ≠ 1 by omega] using h2
  have h3 := specialize _ _ m a h2'
  have h3' : FormulaProves (trichotomy a (.var (m+1))) := by
    simpa [FirstOrder.Language.Term.subst, show m+1 ≠ m by omega] using h3
  have h4 := specialize _ _ (m+1) b h3'
  simpa [FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh a (m+1) b fa] using h4

end PASoundness.PeanoOrderTotality
