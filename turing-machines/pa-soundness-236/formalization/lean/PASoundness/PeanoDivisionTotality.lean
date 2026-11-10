import PASoundness.PeanoDivisionSuccessor

/-! PA division with remainder: finite proof construction in genuine arithmetic. -/
namespace PASoundness.PeanoDivisionTotality
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoAdditionAssociative PeanoMultiplication CompactArithmetic PeanoDivisionSuccessor

/-- A literal quotient/remainder equation with its strict remainder bound. -/
def row (x q m r : Peano.Term) : Peano.Formula :=
  (x.equal (add (mul q m) r)) ⊓ less r m

/-- The two quantified names are fixed for the variable-template construction;
when applying to arbitrary terms use `division`, which substitutes capture-safely. -/
def rows (x m : Peano.Term) : Peano.Formula :=
  FOL.existsAt 2 (FOL.existsAt 3 (row x (.var 2) m (.var 3)))

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


def nextRow (q r : Peano.Term) : Peano.Formula := row (succ (.var 0)) q (.var 1) r
def nextDivision : Peano.Formula := rows (succ (.var 0)) (.var 1)

private theorem package_inc : FormulaProves ((nextRow (.var 2) (succ (.var 3))).imp nextDivision) := by
  have hinner : FormulaProves ((nextRow (.var 2) (succ (.var 3))).imp
      (FOL.existsAt 3 (nextRow (.var 2) (.var 3)))) := by
    have h := FOL.Derivation.existsIntro (A := Peano.Axiom) (nextRow (.var 2) (.var 3)) 3 (succ (.var 3))
    simpa [FOL.substAt, nextRow, row, subst_and, FOL.equality_subst, add_subst, mul_subst,
      less_subst, succ_subst, FirstOrder.Language.Term.subst] using h
  have houter : FormulaProves ((FOL.existsAt 3 (nextRow (.var 2) (.var 3))).imp nextDivision) := by
    simpa only [nextDivision, rows, nextRow, SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) (FOL.existsAt 3 (nextRow (.var 2) (.var 3))) 2 (.var 2))
  exact FOL.Derivation.compose hinner houter

private theorem package_wrap : FormulaProves ((nextRow (succ (.var 2)) zero).imp nextDivision) := by
  have hinner : FormulaProves ((nextRow (succ (.var 2)) zero).imp
      (FOL.existsAt 3 (nextRow (succ (.var 2)) (.var 3)))) := by
    have h := FOL.Derivation.existsIntro (A := Peano.Axiom) (nextRow (succ (.var 2)) (.var 3)) 3 zero
    simpa [FOL.substAt, nextRow, row, subst_and, FOL.equality_subst, add_subst, mul_subst,
      less_subst, succ_subst, PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst] using h
  have he : FOL.substAt (FOL.existsAt 3 (nextRow (.var 2) (.var 3))) 2 (succ (.var 2)) =
      FOL.existsAt 3 (nextRow (succ (.var 2)) (.var 3)) := by
    simp [FOL.substAt, nextRow, row, FOL.existsAt, FOL.allAt, less, lessTemplate, exAt, v,
      Peano.add, Peano.mul, Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
      FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.relabelAux, Min.min]
    repeat' first
      | rfl
      | constructor
      | (congr 1; funext i; fin_cases i <;>
          dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])
  have houter : FormulaProves ((FOL.existsAt 3 (nextRow (succ (.var 2)) (.var 3))).imp nextDivision) := by
    have h := FOL.Derivation.existsIntro (A := Peano.Axiom) (FOL.existsAt 3 (nextRow (.var 2) (.var 3))) 2 (succ (.var 2))
    rw [he] at h
    simpa only [nextDivision, rows, nextRow] using h
  exact FOL.Derivation.compose hinner houter

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

/-- A specific bounded row can be packed into successor witnesses. -/
theorem row_advance : FormulaProves
    ((row (.var 0) (.var 2) (.var 1) (.var 3)).imp nextDivision) := by
  let A := row (.var 0) (.var 2) (.var 1) (.var 3)
  let B := nextRow (.var 2) (succ (.var 3))
  let C := nextRow (succ (.var 2)) zero
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hrow : FOL.Context Peano.Axiom [A] A := FOL.Context.head [] A
  have he : FOL.Context Peano.Axiom [A]
      ((.var 0 : Peano.Term).equal (add (mul (.var 2) (.var 1)) (.var 3))) :=
    FOL.Context.conjunctionLeft hrow
  have hl : FOL.Context Peano.Axiom [A] (less (.var 3) (.var 1)) :=
    FOL.Context.conjunctionRight hrow
  have hcases : FOL.Context Peano.Axiom [A] (B ⊔ C) :=
    .mp (.mp (.closed (successor_rows (.var 0) (.var 2) (.var 1) (.var 3))) he) hl
  exact or_elim hcases (.closed package_inc) (.closed package_wrap)

/-- PA advances the doubly existential quotient/remainder relation by one. -/
theorem rows_advance : FormulaProves
    ((rows (.var 0) (.var 1)).imp (rows (succ (.var 0)) (.var 1))) := by
  have hf3 : 3 ∉ nextDivision.freeVarFinset := by decide
  have h3 := PeanoBitPositionReduction.exists_elim 3 hf3 row_advance
  have hf2 : 2 ∉ nextDivision.freeVarFinset := by decide
  have h2 := PeanoBitPositionReduction.exists_elim 2 hf2 h3
  simpa only [rows, nextDivision] using h2

/-- PA derives the zero-dividend case from a positive modulus. -/
theorem rows_zero : FormulaProves
    ((less zero (.var 1)).imp (rows zero (.var 1))) := by
  have hrow := zero_quotient_row zero (.var 1)
  have hinner : FormulaProves ((row zero zero (.var 1) zero).imp
      (FOL.existsAt 3 (row zero zero (.var 1) (.var 3)))) := by
    have h := FOL.Derivation.existsIntro (A := Peano.Axiom)
      (row zero zero (.var 1) (.var 3)) 3 zero
    simpa [FOL.substAt, row, subst_and, FOL.equality_subst, add_subst, mul_subst,
      less_subst, PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst] using h
  have he : FOL.substAt (FOL.existsAt 3 (row zero (.var 2) (.var 1) (.var 3))) 2 zero =
      FOL.existsAt 3 (row zero zero (.var 1) (.var 3)) := by
    simp [FOL.substAt, row, FOL.existsAt, FOL.allAt, less, lessTemplate, exAt, v,
      Peano.add, Peano.mul, Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
      FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.relabelAux, Min.min]
    repeat' first
      | rfl
      | constructor
      | (congr 1; funext i; fin_cases i <;>
          dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])
  have houter : FormulaProves ((FOL.existsAt 3 (row zero zero (.var 1) (.var 3))).imp
      (rows zero (.var 1))) := by
    have h := FOL.Derivation.existsIntro (A := Peano.Axiom)
      (FOL.existsAt 3 (row zero (.var 2) (.var 1) (.var 3))) 2 zero
    rw [he] at h
    simpa only [rows] using h
  exact FOL.Derivation.compose (FOL.Derivation.compose hrow hinner) houter


/-- Quantified division formula on free names 0 (dividend) and 1 (modulus). -/
def divisionTemplate : Peano.Formula := rows (.var 0) (.var 1)

/-- Capture-safe substitution into the quantified division formula. -/
def division (x m : Peano.Term) : Peano.Formula :=
  divisionTemplate.subst (fun y => if y = 0 then x else if y = 1 then m else zero)

/-- In the standard arithmetic structure this formula is ordinary division
with remainder. This semantic fact is separate from the PA proof construction. -/
theorem division_realize (x m : Peano.Term) (ρ : Nat → Nat) :
    (division x m).Realize ρ ↔
      ∃ q r : Nat, x.realize ρ = q * m.realize ρ + r ∧ r < m.realize ρ := by
  classical
  simp [division, divisionTemplate, rows, row, FOL.existsAt, FOL.realize_allAt,
    FOL.realize_subst, Classical.not_forall, Peano.realize_add, Peano.realize_mul]

private theorem division_subst (x m : Peano.Term) (σ : Nat → Peano.Term) :
    (division x m).subst σ = division (x.subst σ) (m.subst σ) := by
  unfold division
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1]

private theorem template_freeVars : divisionTemplate.freeVarFinset = {0,1} := by decide

private theorem template_as_division : division (.var 0) (.var 1) = divisionTemplate := by
  unfold division
  calc
    divisionTemplate.subst (fun y => if y = 0 then .var 0 else if y = 1 then .var 1 else zero) =
        divisionTemplate.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      simp only [template_freeVars, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> rfl
    _ = divisionTemplate := SyntaxTransport.formula_subst_var _

private theorem template_zero : FOL.substAt divisionTemplate 0 zero =
    rows zero (.var 1) := by
  simp [FOL.substAt, divisionTemplate, rows, row, FOL.existsAt, FOL.allAt,
    less, lessTemplate, exAt, v, Peano.add, Peano.mul, Peano.succ, Peano.zero,
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

private theorem template_succ : FOL.substAt divisionTemplate 0 (succ (.var 0)) =
    rows (succ (.var 0)) (.var 1) := by
  simp [FOL.substAt, divisionTemplate, rows, row, FOL.existsAt, FOL.allAt,
    less, lessTemplate, exAt, v, Peano.add, Peano.mul, Peano.succ, Peano.zero,
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

private def inductionBody : Peano.Formula :=
  (less zero (.var 1)).imp divisionTemplate

private theorem induction_zero : FOL.substAt inductionBody 0 zero =
    ((less zero (.var 1)).imp (rows zero (.var 1))) := by
  unfold inductionBody
  change ((less zero (.var 1)).subst (fun y => if y = 0 then zero else .var y)).imp
    (FOL.substAt divisionTemplate 0 zero) = _
  rw [template_zero]
  simp [less_subst, PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst]

private theorem induction_succ : FOL.substAt inductionBody 0 (succ (.var 0)) =
    ((less zero (.var 1)).imp (rows (succ (.var 0)) (.var 1))) := by
  unfold inductionBody
  change ((less zero (.var 1)).subst (fun y => if y = 0 then succ (.var 0) else .var y)).imp
    (FOL.substAt divisionTemplate 0 (succ (.var 0))) = _
  rw [template_succ]
  simp [less_subst, PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst]

/-- Induction on the dividend, given explicit base and successor proof data. -/
private theorem variables_from_steps
    (hbase : FormulaProves ((less zero (.var 1)).imp (rows zero (.var 1))))
    (hstep : FormulaProves (divisionTemplate.imp (rows (succ (.var 0)) (.var 1)))) :
    FormulaProves ((less zero (.var 1)).imp divisionTemplate) := by
  have hbase' : FormulaProves (FOL.substAt inductionBody 0 zero) := by
    rw [induction_zero]
    exact hbase
  have hstep' : FormulaProves (inductionBody.imp (FOL.substAt inductionBody 0 (succ (.var 0)))) := by
    rw [induction_succ]
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hp : FOL.Context Peano.Axiom [less zero (.var 1), inductionBody]
        (less zero (.var 1)) := FOL.Context.head _ _
    have ih : FOL.Context Peano.Axiom [less zero (.var 1), inductionBody] inductionBody :=
      FOL.Context.under (FOL.Context.head [] inductionBody) _
    have hd : FOL.Context Peano.Axiom [less zero (.var 1), inductionBody] divisionTemplate :=
      .mp ih hp
    exact .mp (.closed hstep) hd
  have hall : FormulaProves (FOL.allAt 0 inductionBody) :=
    .mp (.mp (.axiom (.induction inductionBody 0)) hbase') (.generalize 0 hstep')
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim inductionBody 0 (.var 0))) hall
  simpa only [SyntaxTransport.substAt_self, inductionBody] using h

private def totalityRelation (x m : Peano.Term) : Peano.Formula :=
  (less zero m).imp (division x m)

private theorem specialize (x m : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (totalityRelation x m)) : FormulaProves (totalityRelation
      (x.subst (fun y => if y = name then t else .var y))
      (m.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (totalityRelation x m) name t))
    (.generalize name h)
  simpa only [FOL.substAt, totalityRelation, subst_imp, division_subst, less_subst,
    PeanoArithmetic.zero_subst] using h₁

/-- A capture-safe specialization of the two-variable totality schema. -/
private theorem totality_from_variables
    (hvar : FormulaProves (totalityRelation (.var 0) (.var 1))) (x m : Peano.Term) :
    FormulaProves ((less zero m).imp (division x m)) := by
  let support := x.varFinset ∪ m.varFinset
  let k := support.sup id + 2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have fresh (j : Nat) (hj : k ≤ j) : j ∉ support := by
    intro h
    have hle : j ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [k] at hj
    omega
  have hx : k+1 ∉ x.varFinset := by
    intro h
    apply fresh (k+1) (by omega)
    simp [support, h]
  have h1 := specialize _ _ 0 (.var k) hvar
  have h1' : FormulaProves (totalityRelation (.var k) (.var 1)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ 1 (.var (k+1)) h1'
  have h2' : FormulaProves (totalityRelation (.var k) (.var (k+1))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 1 by omega] using h2
  have h3 := specialize _ _ k x h2'
  have h3' : FormulaProves (totalityRelation x (.var (k+1))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega] using h3
  have h4 := specialize _ _ (k+1) m h3'
  simpa [totalityRelation, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh x (k+1) m hx] using h4

/-- PA proves ordinary division with remainder for arbitrary dividend and
positive modulus terms. The formula `division` uses capture-safe substitution
into the displayed two-witness quotient/remainder template. -/
theorem division_totality (x m : Peano.Term) :
    FormulaProves ((less zero m).imp (division x m)) := by
  have hv : FormulaProves ((less zero (.var 1)).imp divisionTemplate) :=
    variables_from_steps rows_zero rows_advance
  have hv' : FormulaProves (totalityRelation (.var 0) (.var 1)) := by
    simpa only [totalityRelation, template_as_division] using hv
  exact totality_from_variables hv' x m

end PASoundness.PeanoDivisionTotality
