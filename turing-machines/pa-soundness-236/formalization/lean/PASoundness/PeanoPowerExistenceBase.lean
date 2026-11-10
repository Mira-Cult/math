import PASoundness.PeanoBetaUnique
import PASoundness.PeanoEmptyBitSet
import PASoundness.PeanoMulOne
import PASoundness.PeanoPowerSingleton

/-! Literal beta-row construction towards the power-trace existence base. -/
namespace PASoundness.PeanoPowerExistenceBase
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not, subst_imp, subst_not]

private def betaRow (q : Peano.Term) : Peano.Formula :=
  ((.var 0 : Peano.Term).equal (add (mul q (modulus (.var 1) (.var 2))) (.var 3))) ⊓
    (less (.var 3) (modulus (.var 1) (.var 2)))

private theorem beta_template_syntax : betaTemplate = FOL.existsAt 4 (betaRow (.var 4)) := by rfl

private theorem beta_template_as_beta : beta (.var 0) (.var 1) (.var 2) (.var 3) = betaTemplate := by
  unfold beta
  calc
    betaTemplate.subst (fun x => match x with
      | 0 => .var 0 | 1 => .var 1 | 2 => .var 2 | 3 => .var 3 | _ => zero) =
        betaTemplate.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro x hx
      simp only [betaTemplate_freeVars, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> rfl
    _ = betaTemplate := SyntaxTransport.formula_subst_var _

private theorem beta_row_subst : FOL.substAt (betaRow (.var 4)) 4 (.var 5) = betaRow (.var 5) := by
  simp [FOL.substAt, betaRow, subst_and, FOL.equality_subst, add_subst, mul_subst, less_subst,
    modulus, succ_subst, FirstOrder.Language.Term.subst]

/-- A concrete quotient equation and a strict remainder bound give the
literal beta formula in PA; the quotient witness is variable 5. -/
theorem beta_intro_vars :
    FormulaProves
      (((.var 0 : Peano.Term).equal
        (add (mul (.var 5) (modulus (.var 1) (.var 2))) (.var 3))).imp
        ((less (.var 3) (modulus (.var 1) (.var 2))).imp
          (beta (.var 0) (.var 1) (.var 2) (.var 3)))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hrow : FOL.Context Peano.Axiom
      [less (.var 3) (modulus (.var 1) (.var 2)),
        (.var 0 : Peano.Term).equal (add (mul (.var 5) (modulus (.var 1) (.var 2))) (.var 3))]
      (betaRow (.var 5)) :=
    FOL.Context.conjunctionIntro (FOL.Context.under (FOL.Context.head [] _) _)
      (FOL.Context.head _ _)
  have hintro := FOL.Derivation.existsIntro (A := Peano.Axiom) (betaRow (.var 4)) 4 (.var 5)
  rw [beta_row_subst] at hintro
  rw [beta_template_as_beta, beta_template_syntax]
  exact .mp (.closed hintro) hrow

private def introRelation (b c i r q : Peano.Term) : Peano.Formula :=
  (b.equal (add (mul q (modulus c i)) r)).imp
    ((less r (modulus c i)).imp (beta b c i r))

private theorem specialize (b c i r q : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (introRelation b c i r q)) : FormulaProves (introRelation
      (b.subst (fun y => if y = name then t else .var y))
      (c.subst (fun y => if y = name then t else .var y))
      (i.subst (fun y => if y = name then t else .var y))
      (r.subst (fun y => if y = name then t else .var y))
      (q.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (introRelation b c i r q) name t))
    (.generalize name h)
  simpa only [FOL.substAt, introRelation, subst_imp, FOL.equality_subst, add_subst, mul_subst,
    less_subst, beta_subst, modulus, succ_subst] using h₁

/-- From a concrete quotient equation and strict remainder bound, PA derives
the actual beta formula for arbitrary terms, with a capture-safe quotient
witness even when the input terms share free variables. -/
theorem beta_intro (b c i r q : Peano.Term) :
    FormulaProves ((b.equal (add (mul q (modulus c i)) r)).imp
      ((less r (modulus c i)).imp (beta b c i r))) := by
  let support := b.varFinset ∪ c.varFinset ∪ i.varFinset ∪ r.varFinset ∪ q.varFinset
  let k := support.sup id + 6
  have hk : 6 ≤ k := by dsimp [k]; omega
  have fresh (n : Nat) (hn : k ≤ n) : n ∉ support := by
    intro h
    have hle : n ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [k] at hn
    omega
  have fb (n : Nat) (hn : k ≤ n) : n ∉ b.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have fc (n : Nat) (hn : k ≤ n) : n ∉ c.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have fi (n : Nat) (hn : k ≤ n) : n ∉ i.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have fr (n : Nat) (hn : k ≤ n) : n ∉ r.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have h1 := specialize _ _ _ _ _ 0 (.var k) beta_intro_vars
  have h1' : FormulaProves (introRelation (.var k) (.var 1) (.var 2) (.var 3) (.var 5)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ _ _ _ 1 (.var (k+1)) h1'
  have h2' : FormulaProves (introRelation (.var k) (.var (k+1)) (.var 2) (.var 3) (.var 5)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 1 by omega] using h2
  have h3 := specialize _ _ _ _ _ 2 (.var (k+2)) h2'
  have h3' : FormulaProves (introRelation (.var k) (.var (k+1)) (.var (k+2)) (.var 3) (.var 5)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 2 by omega,
      show k+1 ≠ 2 by omega] using h3
  have h4 := specialize _ _ _ _ _ 3 (.var (k+3)) h3'
  have h4' : FormulaProves (introRelation (.var k) (.var (k+1)) (.var (k+2)) (.var (k+3)) (.var 5)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 3 by omega,
      show k+1 ≠ 3 by omega, show k+2 ≠ 3 by omega] using h4
  have h5 := specialize _ _ _ _ _ 5 (.var (k+4)) h4'
  have h5' : FormulaProves (introRelation (.var k) (.var (k+1)) (.var (k+2)) (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 5 by omega,
      show k+1 ≠ 5 by omega, show k+2 ≠ 5 by omega, show k+3 ≠ 5 by omega] using h5
  have h6 := specialize _ _ _ _ _ k b h5'
  have h6' : FormulaProves (introRelation b (.var (k+1)) (.var (k+2)) (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega,
      show k+2 ≠ k by omega, show k+3 ≠ k by omega, show k+4 ≠ k by omega] using h6
  have h7 := specialize _ _ _ _ _ (k+1) c h6'
  have h7' : FormulaProves (introRelation b c (.var (k+2)) (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+1) c (fb _ (by omega)),
      show k+2 ≠ k+1 by omega, show k+3 ≠ k+1 by omega, show k+4 ≠ k+1 by omega] using h7
  have h8 := specialize _ _ _ _ _ (k+2) i h7'
  have h8' : FormulaProves (introRelation b c i (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+2) i (fb _ (by omega)),
      FOL.term_subst_fresh c (k+2) i (fc _ (by omega)),
      show k+3 ≠ k+2 by omega, show k+4 ≠ k+2 by omega] using h8
  have h9 := specialize _ _ _ _ _ (k+3) r h8'
  have h9' : FormulaProves (introRelation b c i r (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+3) r (fb _ (by omega)),
      FOL.term_subst_fresh c (k+3) r (fc _ (by omega)),
      FOL.term_subst_fresh i (k+3) r (fi _ (by omega)), show k+4 ≠ k+3 by omega] using h9
  have h10 := specialize _ _ _ _ _ (k+4) q h9'
  simpa [introRelation, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh b (k+4) q (fb _ (by omega)),
    FOL.term_subst_fresh c (k+4) q (fc _ (by omega)),
    FOL.term_subst_fresh i (k+4) q (fi _ (by omega)),
    FOL.term_subst_fresh r (k+4) q (fr _ (by omega))] using h10

/-- The actual zero-index, value-one beta row has concrete code parameters
`b=1`, `c=1` and quotient witness zero, as an object-level PA derivation. -/
theorem beta_one_row : FormulaProves (beta (succ zero) (succ zero) zero (succ zero)) := by
  let one : Peano.Term := succ zero
  let m : Peano.Term := modulus one zero
  have hrow : FormulaProves (one.equal (add (mul zero m) one)) := by
    have h₁ := FOL.Derivation.mp (PeanoAdditionAssociative.add_left_congr one (mul zero m) zero)
      (PeanoMultiplication.zero_mul m)
    exact FOL.Derivation.eqSymm (FOL.Derivation.eqTrans h₁ (zero_add one))
  have hm : FormulaProves (m.equal (succ one)) := by
    have h := FOL.Derivation.mp (PeanoOrderIrreflexive.succ_congr (mul one one) one)
      (PeanoMultiplication.mul_one one)
    exact h
  have hbound : FormulaProves (less one m) := by
    have hone : FormulaProves (less one (succ one)) := PeanoPowerTransition.self_less_succ one
    exact .mp (.mp (PeanoMultiplyQuotientStep.less_right_congr one (succ one) m)
      (FOL.Derivation.eqSymm hm)) hone
  exact .mp (.mp (beta_intro one one zero one zero) hrow) hbound

/-- The actual transition body restricted to indices below zero. -/
def zeroTrace (b c : Peano.Term) : Peano.Formula :=
  FOL.allAt 4 ((less (.var 4) zero).imp (PeanoPowerTransition.transition b c (.var 4) 5 6))

/-- PA proves that the zero-bounded transition obligation is vacuous. -/
theorem zero_trace (b c : Peano.Term) : FormulaProves (zeroTrace b c) := by
  apply FOL.Derivation.generalize 4
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  exact FOL.Context.explode _
    (.mp (.closed (PeanoEmptyBitSet.no_less_zero (.var 4))) (FOL.Context.head [] _))

private def baseBody (b c : Peano.Term) : Peano.Formula :=
  (beta b c zero (succ zero)) ⊓ ((beta b c zero (succ zero)) ⊓ zeroTrace b c)

private theorem base_body_one : FormulaProves (baseBody (succ zero) (succ zero)) := by
  apply FOL.Context.closeEmpty
  exact FOL.Context.conjunctionIntro (.closed beta_one_row)
    (FOL.Context.conjunctionIntro (.closed beta_one_row) (.closed (zero_trace _ _)))

private theorem pow2_zero_one_syntax : pow2 zero (succ zero) =
    FOL.existsAt 2 (FOL.existsAt 3 (baseBody (.var 2) (.var 3))) := by
  simp [pow2, pow2Template, baseBody, zeroTrace, PeanoPowerTransition.transition,
    PeanoPowerTransition.transitionBody, FOL.existsAt, FOL.allAt, beta, betaTemplate,
    less, lessTemplate, modulus, exAt, v, Peano.add, Peano.mul, Peano.succ, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
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

private theorem base_c_syntax :
    FOL.substAt (baseBody (succ zero) (.var 3)) 3 (succ zero) =
      baseBody (succ zero) (succ zero) := by
  simp [FOL.substAt, baseBody, zeroTrace, PeanoPowerTransition.transition,
    PeanoPowerTransition.transitionBody, FOL.existsAt, FOL.allAt, beta, betaTemplate,
    less, lessTemplate, modulus, exAt, v, Peano.add, Peano.mul, Peano.succ, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
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
      all_goals
        congr 1
        funext k
        fin_cases k
        congr 1
        funext z
        exact Fin.elim0 z

private theorem base_b_syntax :
    FOL.substAt (FOL.existsAt 3 (baseBody (.var 2) (.var 3))) 2 (succ zero) =
      FOL.existsAt 3 (baseBody (succ zero) (.var 3)) := by
  simp [FOL.substAt, baseBody, zeroTrace, PeanoPowerTransition.transition,
    PeanoPowerTransition.transitionBody, FOL.existsAt, FOL.allAt, beta, betaTemplate,
    less, lessTemplate, modulus, exAt, v, Peano.add, Peano.mul, Peano.succ, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
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

/-- PA derives the literal zero-index power trace with endpoint one, using
the explicit beta-code parameters `b=1`, `c=1`. This proves an actual
object-level existence base, not merely a semantic computation. -/
theorem pow2_zero_one : FormulaProves (pow2 zero (succ zero)) := by
  have hc := FOL.Derivation.existsIntro (A := Peano.Axiom) (baseBody (succ zero) (.var 3)) 3 (succ zero)
  rw [base_c_syntax] at hc
  have hC : FormulaProves (FOL.existsAt 3 (baseBody (succ zero) (.var 3))) :=
    .mp hc base_body_one
  have hb := FOL.Derivation.existsIntro (A := Peano.Axiom)
    (FOL.existsAt 3 (baseBody (.var 2) (.var 3))) 2 (succ zero)
  rw [base_b_syntax] at hb
  rw [pow2_zero_one_syntax]
  exact .mp hb hC

/-- PA proves the existential zero-index power trace by exhibiting one. -/
theorem exists_pow2_zero : FormulaProves (FOL.existsAt 1 (pow2 zero (.var 1))) := by
  have h := FOL.Derivation.existsIntro (A := Peano.Axiom) (pow2 zero (.var 1)) 1 (succ zero)
  have hs : FOL.substAt (pow2 zero (.var 1)) 1 (succ zero) = pow2 zero (succ zero) := by
    simp [FOL.substAt, pow2_subst, PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst]
  rw [hs] at h
  exact .mp h pow2_zero_one

/-- The concrete nonempty bit code one has its zero-index bit in PA. -/
theorem one_has_zero_bit : FormulaProves (bitFormula (succ zero) zero) :=
  .mp (PeanoPowerSingleton.power_trace_sets_bit zero (succ zero)) pow2_zero_one

end PASoundness.PeanoPowerExistenceBase
