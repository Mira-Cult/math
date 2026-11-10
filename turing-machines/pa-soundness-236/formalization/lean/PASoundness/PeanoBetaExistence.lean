import PASoundness.PeanoDivisionTotality

/-! Existence of an output for the literal beta row inside PA. -/
namespace PASoundness.PeanoBetaExistence
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoDivisionTotality

/-- Exact existential beta-output formula on free names 0, 1 and 2. -/
def betaExistsTemplate : Peano.Formula :=
  FOL.existsAt 3 (beta (.var 0) (.var 1) (.var 2) (.var 3))

/-- Capture-safe application of the literal beta-output formula to terms. -/
def betaExists (b c i : Peano.Term) : Peano.Formula :=
  betaExistsTemplate.subst (fun y => match y with
    | 0 => b | 1 => c | 2 => i | _ => zero)

private def matrix : Peano.Formula :=
  (((.var 0 : Peano.Term).equal (add (mul (.var 4) (modulus (.var 1) (.var 2))) (.var 3))) ⊓
    (less (.var 3) (modulus (.var 1) (.var 2))))

theorem beta_syntax : beta (.var 0) (.var 1) (.var 2) (.var 3) = FOL.existsAt 4 matrix := by
  have he : beta (.var 0) (.var 1) (.var 2) (.var 3) = betaTemplate := by
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
  rw [he]
  rfl

theorem division_syntax :
    division (.var 0) (modulus (.var 1) (.var 2)) =
      FOL.existsAt 4 (FOL.existsAt 3 matrix) := by
  simp [division, divisionTemplate, rows, row, matrix, FOL.existsAt, FOL.allAt,
    less, lessTemplate, exAt, modulus, v, Peano.add, Peano.mul, Peano.succ, Peano.zero,
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

  congr 1
  funext i
  fin_cases i
  congr 1
  funext j
  fin_cases j <;> simp [FirstOrder.Language.Term.relabel]

/-- Swap the actual quotient/remainder witnesses using PA derivations. -/
theorem swap_witnesses :
    FormulaProves ((FOL.existsAt 4 (FOL.existsAt 3 matrix)).imp
      (FOL.existsAt 3 (FOL.existsAt 4 matrix))) := by
  let goal : Peano.Formula := FOL.existsAt 3 (FOL.existsAt 4 matrix)
  have h4 : FormulaProves (matrix.imp (FOL.existsAt 4 matrix)) := by
    simpa only [SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) matrix 4 (.var 4))
  have h3 : FormulaProves ((FOL.existsAt 4 matrix).imp goal) := by
    simpa only [goal, SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) (FOL.existsAt 4 matrix) 3 (.var 3))
  have both := FOL.Derivation.compose h4 h3
  have fresh3 : 3 ∉ goal.freeVarFinset := by decide
  have e3 := PeanoBitPositionReduction.exists_elim 3 fresh3 both
  have fresh4 : 4 ∉ goal.freeVarFinset := by decide
  exact PeanoBitPositionReduction.exists_elim 4 fresh4 e3

/-- Obtain an explicit beta-output witness by transporting division's two witnesses. -/
theorem beta_exists_vars :
    FormulaProves (FOL.existsAt 3 (beta (.var 0) (.var 1) (.var 2) (.var 3))) := by
  have hpos := PeanoOrderTotality.zero_less_succ (mul (succ (.var 2)) (.var 1))
  have hdiv := FOL.Derivation.mp
    (division_totality (.var 0) (modulus (.var 1) (.var 2))) hpos
  have hdiv' : FormulaProves (FOL.existsAt 4 (FOL.existsAt 3 matrix)) := by
    rwa [division_syntax] at hdiv
  have h := FOL.Derivation.mp swap_witnesses hdiv'
  simpa only [beta_syntax] using h


/-- Its standard meaning is that the literal beta relation has an output. This
semantic theorem is separate from the object-level PA proof. -/
theorem betaExists_realize (b c i : Peano.Term) (ρ : Nat → Nat) :
    (betaExists b c i).Realize ρ ↔ ∃ r, Beta (b.realize ρ) (c.realize ρ) (i.realize ρ) r := by
  classical
  simp [betaExists, betaExistsTemplate, FOL.existsAt, FOL.realize_allAt,
    FOL.realize_subst, Classical.not_forall]

private theorem betaExists_subst (b c i : Peano.Term) (σ : Nat → Peano.Term) :
    (betaExists b c i).subst σ = betaExists (b.subst σ) (c.subst σ) (i.subst σ) := by
  unfold betaExists
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  match y with
  | 0 | 1 | 2 => rfl
  | _+3 => exact PeanoArithmetic.zero_subst σ

private theorem template_freeVars : betaExistsTemplate.freeVarFinset = {0,1,2} := by decide

private theorem template_as_betaExists : betaExists (.var 0) (.var 1) (.var 2) = betaExistsTemplate := by
  unfold betaExists
  calc
    betaExistsTemplate.subst (fun y => match y with
      | 0 => .var 0 | 1 => .var 1 | 2 => .var 2 | _ => zero) =
        betaExistsTemplate.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      simp only [template_freeVars, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> rfl
    _ = betaExistsTemplate := SyntaxTransport.formula_subst_var _

private theorem specialize (b c i : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (betaExists b c i)) : FormulaProves (betaExists
      (b.subst (fun y => if y = name then t else .var y))
      (c.subst (fun y => if y = name then t else .var y))
      (i.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (betaExists b c i) name t))
    (.generalize name h)
  simpa only [FOL.substAt, betaExists_subst] using h₁

private theorem betaExists_from_variables
    (hvar : FormulaProves (betaExists (.var 0) (.var 1) (.var 2))) (b c i : Peano.Term) :
    FormulaProves (betaExists b c i) := by
  let support := b.varFinset ∪ c.varFinset ∪ i.varFinset
  let k := support.sup id + 3
  have hk : 3 ≤ k := by dsimp [k]; omega
  have fresh (j : Nat) (hj : k ≤ j) : j ∉ support := by
    intro h
    have hle : j ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [k] at hj
    omega
  have fb (j : Nat) (hj : k ≤ j) : j ∉ b.varFinset := by
    intro h; apply fresh j hj; simp [support, h]
  have fc (j : Nat) (hj : k ≤ j) : j ∉ c.varFinset := by
    intro h; apply fresh j hj; simp [support, h]
  have h1 := specialize _ _ _ 0 (.var k) hvar
  have h1' : FormulaProves (betaExists (.var k) (.var 1) (.var 2)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ _ 1 (.var (k+1)) h1'
  have h2' : FormulaProves (betaExists (.var k) (.var (k+1)) (.var 2)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 1 by omega] using h2
  have h3 := specialize _ _ _ 2 (.var (k+2)) h2'
  have h3' : FormulaProves (betaExists (.var k) (.var (k+1)) (.var (k+2))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 2 by omega,
      show k+1 ≠ 2 by omega] using h3
  have h4 := specialize _ _ _ k b h3'
  have h4' : FormulaProves (betaExists b (.var (k+1)) (.var (k+2))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega,
      show k+2 ≠ k by omega] using h4
  have h5 := specialize _ _ _ (k+1) c h4'
  have h5' : FormulaProves (betaExists b c (.var (k+2))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+1) c (fb _ (by omega)),
      show k+2 ≠ k+1 by omega] using h5
  have h6 := specialize _ _ _ (k+2) i h5'
  simpa [FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh b (k+2) i (fb _ (by omega)),
    FOL.term_subst_fresh c (k+2) i (fc _ (by omega))] using h6

/-- For arbitrary terms, PA derives that the literal beta relation has an
output. The term substitution into the existential template is capture-safe. -/
theorem beta_exists (b c i : Peano.Term) : FormulaProves (betaExists b c i) := by
  have hv : FormulaProves (betaExists (.var 0) (.var 1) (.var 2)) := by
    simpa only [template_as_betaExists, betaExistsTemplate] using beta_exists_vars
  exact betaExists_from_variables hv b c i

end PASoundness.PeanoBetaExistence
