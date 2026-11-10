import PASoundness.PeanoBitPositionReduction
import PASoundness.PeanoMultiplication

/-! Object-level PA projection of the actual beta row's remainder bound. -/
namespace PASoundness.PeanoBetaBound
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic

private def body : Peano.Formula :=
  ((v 0).equal (add (mul (v 4) (modulus (v 1) (v 2))) (v 3))) ⊓
    (less (v 3) (modulus (v 1) (v 2)))
private def bound : Peano.Formula := less (v 3) (modulus (v 1) (v 2))

/-- The bound on the remainder follows from the actual beta-template row by
finite logical elimination of its quotient witness. -/
theorem template_remainder_bound : FormulaProves (betaTemplate.imp bound) := by
  have hbody : FormulaProves (body.imp bound) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    exact FOL.Context.conjunctionRight (FOL.Context.head [] body)
  have hfresh : 4 ∉ bound.freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 4 hfresh hbody
  simpa only [betaTemplate, CompactArithmetic.exAt, FOL.existsAt, body, bound] using h

private theorem template_as_beta :
    beta (.var 0) (.var 1) (.var 2) (.var 3) = betaTemplate := by
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

/-- PA derives the literal beta remainder bound with four free row variables. -/
theorem beta_remainder_bound :
    FormulaProves ((beta (.var 0) (.var 1) (.var 2) (.var 3)).imp
      (less (.var 3) (modulus (.var 1) (.var 2)))) := by
  simpa only [template_as_beta, bound, v] using template_remainder_bound

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private def rowBound (b c i r : Peano.Term) : Peano.Formula :=
  (beta b c i r).imp (less r (modulus c i))

private theorem specialize (b c i r : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (rowBound b c i r)) :
    FormulaProves (rowBound
      (b.subst (fun y => if y = name then t else .var y))
      (c.subst (fun y => if y = name then t else .var y))
      (i.subst (fun y => if y = name then t else .var y))
      (r.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (rowBound b c i r) name t))
    (.generalize name h)
  simpa only [FOL.substAt, rowBound, subst_imp, beta_subst, less_subst, modulus,
    succ_subst, mul_subst] using h₁

/-- PA derives the actual beta remainder bound for arbitrary arithmetic
terms. Four fresh temporary names prevent substitution into a term inserted
at an earlier step, including when the original terms share variables. -/
theorem beta_remainder_bound_all (b c i r : Peano.Term) :
    FormulaProves ((beta b c i r).imp (less r (modulus c i))) := by
  let support := b.varFinset ∪ c.varFinset ∪ i.varFinset ∪ r.varFinset
  let m := support.sup id + 4
  have hm : 4 ≤ m := by dsimp [m]; omega
  have fresh (n : Nat) (hn : m ≤ n) : n ∉ support := by
    intro h
    have hle : n ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [m] at hn
    omega
  have fb (n : Nat) (hn : m ≤ n) : n ∉ b.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have fc (n : Nat) (hn : m ≤ n) : n ∉ c.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have fi (n : Nat) (hn : m ≤ n) : n ∉ i.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have h0 : FormulaProves (rowBound (.var 0) (.var 1) (.var 2) (.var 3)) :=
    beta_remainder_bound
  have h1 := specialize _ _ _ _ 0 (.var m) h0
  have h1' : FormulaProves (rowBound (.var m) (.var 1) (.var 2) (.var 3)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ _ _ 1 (.var (m+1)) h1'
  have h2' : FormulaProves (rowBound (.var m) (.var (m+1)) (.var 2) (.var 3)) := by
    simpa [FirstOrder.Language.Term.subst, show m ≠ 1 by omega] using h2
  have h3 := specialize _ _ _ _ 2 (.var (m+2)) h2'
  have h3' : FormulaProves (rowBound (.var m) (.var (m+1)) (.var (m+2)) (.var 3)) := by
    simpa [FirstOrder.Language.Term.subst, show m ≠ 2 by omega,
      show m+1 ≠ 2 by omega] using h3
  have h4 := specialize _ _ _ _ 3 (.var (m+3)) h3'
  have h4' : FormulaProves (rowBound (.var m) (.var (m+1)) (.var (m+2)) (.var (m+3))) := by
    simpa [FirstOrder.Language.Term.subst, show m ≠ 3 by omega,
      show m+1 ≠ 3 by omega, show m+2 ≠ 3 by omega] using h4
  have h5 := specialize _ _ _ _ m b h4'
  have h5' : FormulaProves (rowBound b (.var (m+1)) (.var (m+2)) (.var (m+3))) := by
    simpa [FirstOrder.Language.Term.subst, show m+1 ≠ m by omega,
      show m+2 ≠ m by omega, show m+3 ≠ m by omega] using h5
  have h6 := specialize _ _ _ _ (m+1) c h5'
  have h6' : FormulaProves (rowBound b c (.var (m+2)) (.var (m+3))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (m+1) c (fb _ (by omega)),
      show m+2 ≠ m+1 by omega, show m+3 ≠ m+1 by omega] using h6
  have h7 := specialize _ _ _ _ (m+2) i h6'
  have h7' : FormulaProves (rowBound b c i (.var (m+3))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (m+2) i (fb _ (by omega)),
      FOL.term_subst_fresh c (m+2) i (fc _ (by omega)), show m+3 ≠ m+2 by omega] using h7
  have h8 := specialize _ _ _ _ (m+3) r h7'
  simpa [rowBound, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh b (m+3) r (fb _ (by omega)),
    FOL.term_subst_fresh c (m+3) r (fc _ (by omega)),
    FOL.term_subst_fresh i (m+3) r (fi _ (by omega))] using h8

/-- The exact zero-index, one-value beta row appearing in the power-template
implies its actual arithmetic modulus exceeds one. This is a syntactic PA
derivation, with no beta uniqueness or power-growth assumption. -/
theorem power_zero_row_bound :
    FormulaProves ((beta (.var 2) (.var 3) zero (succ zero)).imp
      (less (succ zero) (modulus (.var 3) zero))) :=
  beta_remainder_bound_all _ _ _ _

end PASoundness.PeanoBetaBound
