import PASoundness.PeanoPolynomialContext

/-! Explicit quotient witnesses for PA divisibility and multiplication. -/
namespace PASoundness.PeanoDivisibility
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoPolynomialContext

/-- If `d=t*k`, the explicit quotient `t*f` shows `d*f=(t*f)*k`.
The polynomial equality is extracted as a derivation in the same PA context. -/
theorem multiply_preserves_equation (d t k f : Peano.Term) :
    FormulaProves ((d.equal (mul t k)).imp
      ((mul d f).equal (mul (mul t f) k))) := by
  let E := d.equal (mul t k)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply cls_exact
  simp only [cls_mul]
  have he : cls [E] d = cls [E] t * cls [E] k := by
    simpa only [cls_mul] using (cls_sound (FOL.Context.head [] E))
  rw [he]
  ring

/-- Quotient template with free divisor 0 and dividend 1. -/
def dividesTemplate : Peano.Formula :=
  FOL.existsAt 2 ((.var 1 : Peano.Term).equal (mul (.var 2) (.var 0)))

/-- Divisibility applied to arbitrary terms by capture-safe substitution. -/
def divides (k d : Peano.Term) : Peano.Formula :=
  dividesTemplate.subst (fun y => if y = 0 then k else if y = 1 then d else zero)

/-- Standard meaning of the quotient formula, separate from PA derivations. -/
theorem divides_realize (k d : Peano.Term) (ρ : Nat → Nat) :
    (divides k d).Realize ρ ↔ ∃ t : Nat, d.realize ρ = t * k.realize ρ := by
  classical
  simp [divides, dividesTemplate, FOL.existsAt, FOL.realize_allAt,
    FOL.realize_subst, Classical.not_forall, Peano.realize_mul]

private theorem divides_subst (k d : Peano.Term) (σ : Nat → Peano.Term) :
    (divides k d).subst σ = divides (k.subst σ) (d.subst σ) := by
  unfold divides
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1]

private theorem template_freeVars : dividesTemplate.freeVarFinset = {0,1} := by decide

private theorem template_as_divides : divides (.var 0) (.var 1) = dividesTemplate := by
  unfold divides
  calc
    dividesTemplate.subst (fun y => if y = 0 then .var 0 else if y = 1 then .var 1 else zero) =
        dividesTemplate.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      simp only [template_freeVars, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> rfl
    _ = dividesTemplate := SyntaxTransport.formula_subst_var _

private def inputBody : Peano.Formula :=
  (.var 1 : Peano.Term).equal (mul (.var 2) (.var 0))
private def targetBody : Peano.Formula :=
  (mul (.var 1) (.var 3)).equal (mul (.var 4) (.var 0))
private def target : Peano.Formula := FOL.existsAt 4 targetBody

private theorem input_syntax : divides (.var 0) (.var 1) = FOL.existsAt 2 inputBody := by
  have free : dividesTemplate.freeVarFinset = {0,1} := by decide
  unfold divides
  calc
    dividesTemplate.subst (fun y => if y = 0 then .var 0 else if y = 1 then .var 1 else zero) =
        dividesTemplate.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      simp only [free, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> rfl
    _ = dividesTemplate := SyntaxTransport.formula_subst_var _
    _ = FOL.existsAt 2 inputBody := rfl

private theorem target_syntax : divides (.var 0) (mul (.var 1) (.var 3)) = target := by
  simp [divides, dividesTemplate, target, targetBody, FOL.existsAt, FOL.allAt,
    Peano.mul, Peano.zero, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst,
    FirstOrder.Language.Term.relabel, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.subst, FirstOrder.Language.BoundedFormula.relabel,
    FirstOrder.Language.BoundedFormula.mapTermRel, FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

theorem row_advance : FormulaProves (inputBody.imp target) := by
  have he : FOL.Context Peano.Axiom [inputBody]
      ((mul (.var 1) (.var 3)).equal (mul (mul (.var 2) (.var 3)) (.var 0))) :=
    .mp (.closed (multiply_preserves_equation (.var 1) (.var 2) (.var 0) (.var 3)))
      (FOL.Context.head [] inputBody)
  have hs : FOL.substAt targetBody 4 (mul (.var 2) (.var 3)) =
      ((mul (.var 1) (.var 3)).equal (mul (mul (.var 2) (.var 3)) (.var 0))) := by
    simp [FOL.substAt, targetBody, FOL.equality_subst, mul_subst, FirstOrder.Language.Term.subst]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.mp (.closed (FOL.Derivation.existsIntro targetBody 4 (mul (.var 2) (.var 3))))
  rw [hs]
  exact he

theorem divides_mul_vars : FormulaProves
    ((divides (.var 0) (.var 1)).imp (divides (.var 0) (mul (.var 1) (.var 3)))) := by
  have hfresh : 2 ∉ target.freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 2 hfresh row_advance
  simpa only [input_syntax, target_syntax] using h


private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private def preserve (k d f : Peano.Term) : Peano.Formula :=
  (divides k d).imp (divides k (mul d f))

private theorem specialize (k d f : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (preserve k d f)) : FormulaProves (preserve
      (k.subst (fun y => if y = name then t else .var y))
      (d.subst (fun y => if y = name then t else .var y))
      (f.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (preserve k d f) name t))
    (.generalize name h)
  simpa only [FOL.substAt, preserve, subst_imp, divides_subst, mul_subst] using h₁

private theorem preserve_from_variables
    (hvar : FormulaProves (preserve (.var 0) (.var 1) (.var 3))) (k d f : Peano.Term) :
    FormulaProves (preserve k d f) := by
  let support := k.varFinset ∪ d.varFinset ∪ f.varFinset
  let n := support.sup id + 4
  have hn : 4 ≤ n := by dsimp [n]; omega
  have fresh (j : Nat) (hj : n ≤ j) : j ∉ support := by
    intro h
    have hle : j ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [n] at hj
    omega
  have fk (j : Nat) (hj : n ≤ j) : j ∉ k.varFinset := by
    intro h; apply fresh j hj; simp [support, h]
  have fd (j : Nat) (hj : n ≤ j) : j ∉ d.varFinset := by
    intro h; apply fresh j hj; simp [support, h]
  have h1 := specialize _ _ _ 0 (.var n) hvar
  have h1' : FormulaProves (preserve (.var n) (.var 1) (.var 3)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ _ 1 (.var (n+1)) h1'
  have h2' : FormulaProves (preserve (.var n) (.var (n+1)) (.var 3)) := by
    simpa [FirstOrder.Language.Term.subst, show n ≠ 1 by omega] using h2
  have h3 := specialize _ _ _ 3 (.var (n+2)) h2'
  have h3' : FormulaProves (preserve (.var n) (.var (n+1)) (.var (n+2))) := by
    simpa [FirstOrder.Language.Term.subst, show n ≠ 3 by omega,
      show n+1 ≠ 3 by omega] using h3
  have h4 := specialize _ _ _ n k h3'
  have h4' : FormulaProves (preserve k (.var (n+1)) (.var (n+2))) := by
    simpa [FirstOrder.Language.Term.subst, show n+1 ≠ n by omega,
      show n+2 ≠ n by omega] using h4
  have h5 := specialize _ _ _ (n+1) d h4'
  have h5' : FormulaProves (preserve k d (.var (n+2))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh k (n+1) d (fk _ (by omega)),
      show n+2 ≠ n+1 by omega] using h5
  have h6 := specialize _ _ _ (n+2) f h5'
  simpa [FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh k (n+2) f (fk _ (by omega)),
    FOL.term_subst_fresh d (n+2) f (fd _ (by omega))] using h6

/-- Every PA-divisible multiple remains divisible by the same term after
multiplication by any factor, via the explicit witness in `row_advance`. -/
theorem divides_mul (k d f : Peano.Term) :
    FormulaProves ((divides k d).imp (divides k (mul d f))) :=
  preserve_from_variables divides_mul_vars k d f

private theorem self_syntax : divides (.var 0) (.var 0) =
    FOL.existsAt 2 ((.var 0 : Peano.Term).equal (mul (.var 2) (.var 0))) := by
  simp [divides, dividesTemplate, FOL.existsAt, FOL.allAt, Peano.mul, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

private theorem zero_syntax : divides (.var 0) zero =
    FOL.existsAt 2 (zero.equal (mul (.var 2) (.var 0))) := by
  simp [divides, dividesTemplate, FOL.existsAt, FOL.allAt, Peano.mul, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

private theorem self_vars : FormulaProves (divides (.var 0) (.var 0)) := by
  rw [self_syntax]
  let body : Peano.Formula := (.var 0 : Peano.Term).equal (mul (.var 2) (.var 0))
  have hs : FOL.substAt body 2 (succ zero) =
      ((.var 0 : Peano.Term).equal (mul (succ zero) (.var 0))) := by
    simp [FOL.substAt, body, FOL.equality_subst, mul_subst, FirstOrder.Language.Term.subst]
  have hi := FOL.Derivation.existsIntro (A := Peano.Axiom) body 2 (succ zero)
  rw [hs] at hi
  exact .mp hi (FOL.Derivation.eqSymm (PeanoArithmetic.one_mul (.var 0)))

private theorem zero_vars : FormulaProves (divides (.var 0) zero) := by
  rw [zero_syntax]
  let body : Peano.Formula := zero.equal (mul (.var 2) (.var 0))
  have hs : FOL.substAt body 2 zero = zero.equal (mul zero (.var 0)) := by
    simp [FOL.substAt, body, FOL.equality_subst, mul_subst, PeanoArithmetic.zero_subst,
      FirstOrder.Language.Term.subst]
  have hi := FOL.Derivation.existsIntro (A := Peano.Axiom) body 2 zero
  rw [hs] at hi
  exact .mp hi (FOL.Derivation.eqSymm (PeanoMultiplication.zero_mul (.var 0)))

/-- Every term divides itself, with the explicit quotient one. -/
theorem divides_self (k : Peano.Term) : FormulaProves (divides k k) := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (divides (.var 0) (.var 0)) 0 k))
    (.generalize 0 self_vars)
  simpa [FOL.substAt, divides_subst, FirstOrder.Language.Term.subst] using h

/-- Every term divides zero, with the explicit quotient zero. -/
theorem divides_zero (k : Peano.Term) : FormulaProves (divides k zero) := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (divides (.var 0) zero) 0 k))
    (.generalize 0 zero_vars)
  simpa [FOL.substAt, divides_subst, PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst] using h


end PASoundness.PeanoDivisibility
