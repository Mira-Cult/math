import PASoundness.PeanoBetaAppendRelation
import PASoundness.PeanoBetaBoundedTotality
import PASoundness.PeanoBetaAppendBound

/-! Specialization of the bounded PA CRT endpoint to desired rows for a
single trace append. The final theorem constructs an append recoding after
discharging bounded row existence; it does not establish power-trace totality. -/
namespace PASoundness.PeanoBetaAppendCRT
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic
open PeanoBetaAppendRelation PeanoBetaBoundedTotality PeanoBetaCRTInvariant PeanoBetaCRTParameter

/-- Bound exceeding every old row and the desired final value. -/
def traceBound : Peano.Term := add (modulus (.var 5) (.var 0)) (add (.var 6) (.var 6))
def endIndex : Peano.Term := succ (succ (.var 0))

def σ (x : Nat) : Peano.Term :=
  if x = 16 then traceBound else if x = 8 then endIndex else .var x

def boundedAppendRows : Peano.Formula := FOL.allAt 2
  ((less (.var 2) endIndex).imp (FOL.existsAt 3
    (appendRelation ⊓ less (.var 3) (succ traceBound))))

def appendSolved : Peano.Formula :=
  (PeanoBetaCRTParameter.boundedSolvedParameter appendRelation).subst σ

private theorem subst_not (φ : Peano.Formula) (s : Nat → Peano.Term) :
    φ.not.subst s = (φ.subst s).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl
private theorem subst_and (φ ψ : Peano.Formula) (s : Nat → Peano.Term) :
    (φ ⊓ ψ).subst s = (φ.subst s) ⊓ (ψ.subst s) := by
  change (φ.imp ψ.not).not.subst s = ((φ.subst s).imp (ψ.subst s).not).not
  rw [subst_not, show (φ.imp ψ.not).subst s = (φ.subst s).imp (ψ.not.subst s) from rfl, subst_not]

private theorem σ_fixes (b : Nat) (hb8 : b ≠ 8) (hb16 : b ≠ 16) : σ b = .var b := by
  simp [σ, hb8, hb16]
private theorem σ_avoids (b : Nat) (hb0 : b ≠ 0) (hb5 : b ≠ 5) (hb6 : b ≠ 6)
    (x : Nat) (hxb : x ≠ b) : b ∉ (σ x).varFinset := by
  by_cases h16 : x = 16
  · subst x
    simp [σ, traceBound, modulus, Peano.add, Peano.mul, Peano.succ,
      FirstOrder.Language.Term.varFinset, hb0, hb5, hb6]
  by_cases h8 : x = 8
  · subst x
    simp [σ, endIndex, Peano.succ, FirstOrder.Language.Term.varFinset, hb0]
  · simp [σ, h16, h8, FirstOrder.Language.Term.varFinset, Ne.symm hxb]

private theorem subst_all (b : Nat) (hb0 : b ≠ 0) (hb5 : b ≠ 5) (hb6 : b ≠ 6)
    (hb8 : b ≠ 8) (hb16 : b ≠ 16) (φ : Peano.Formula) :
    (FOL.allAt b φ).subst σ = FOL.allAt b (φ.subst σ) :=
  PeanoBetaCRTAlignment.arbitrary_subst_all_at σ b (σ_fixes b hb8 hb16)
    (σ_avoids b hb0 hb5 hb6) φ
private theorem subst_exists (b : Nat) (hb0 : b ≠ 0) (hb5 : b ≠ 5) (hb6 : b ≠ 6)
    (hb8 : b ≠ 8) (hb16 : b ≠ 16) (φ : Peano.Formula) :
    (FOL.existsAt b φ).subst σ = FOL.existsAt b (φ.subst σ) :=
  PeanoBetaCRTAlignment.arbitrary_subst_exists_at σ b (σ_fixes b hb8 hb16)
    (σ_avoids b hb0 hb5 hb6) φ

private theorem append_fresh : appendRelation.subst σ = appendRelation := by
  calc
    appendRelation.subst σ = appendRelation.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro x hx
      have hf : appendRelation.freeVarFinset = {0,2,3,4,5,6} := by decide
      rw [hf] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    _ = appendRelation := SyntaxTransport.formula_subst_var _

/-- Exact replacement of both bound variables, preserving the row binder. -/
theorem bounded_rows_syntax : (boundedRows appendRelation).subst σ = boundedAppendRows := by
  unfold boundedRows boundedAppendRows
  rw [subst_all 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  congr 1
  change ((less (.var 2) (.var 8)).subst σ).imp
    ((FOL.existsAt 3 (appendRelation ⊓ less (.var 3) (succ (.var 16)))).subst σ) = _
  rw [subst_exists 3 (by decide) (by decide) (by decide) (by decide) (by decide),
    subst_and, append_fresh]
  simp [less_subst, succ_subst, FirstOrder.Language.Term.subst, σ]

/-- The two ordinary specializations have exactly the simultaneous action σ.
The inserted bound is free of name 8, so the second specialization does not
alter it. -/
theorem specialization_syntax (φ : Peano.Formula) :
    FOL.substAt (FOL.substAt φ 16 traceBound) 8 endIndex = φ.subst σ := by
  unfold FOL.substAt
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext x
  by_cases h16 : x = 16
  · subst x
    simp [σ, traceBound, modulus, add_subst, mul_subst, succ_subst,
      FirstOrder.Language.Term.subst]
  by_cases h8 : x = 8
  · subst x
    simp [σ, FirstOrder.Language.Term.subst]
  · simp [σ, h16, h8, FirstOrder.Language.Term.subst]

/-- The bounded append rows supply one code and one larger beta parameter,
with both occurrences of the requested length specialized. -/
theorem bounded_append_solve : FormulaProves (boundedAppendRows.imp appendSolved) := by
  let F := (boundedRows appendRelation).imp
    (PeanoBetaCRTParameter.boundedSolvedParameter appendRelation)
  have h1 : 1 ∉ appendRelation.freeVarFinset := by decide
  have h : FormulaProves F := bounded_rows_solve appendRelation h1 append_names_safe
  have h16 : FormulaProves (FOL.substAt F 16 traceBound) := .mp
    (.logical (.allElim F 16 traceBound)) (.generalize 16 h)
  have h8 : FormulaProves (FOL.substAt (FOL.substAt F 16 traceBound) 8 endIndex) := .mp
    (.logical (.allElim (FOL.substAt F 16 traceBound) 8 endIndex)) (.generalize 8 h16)
  rw [specialization_syntax] at h8
  change FormulaProves (((boundedRows appendRelation).subst σ).imp
    ((PeanoBetaCRTParameter.boundedSolvedParameter appendRelation).subst σ)) at h8
  simpa only [bounded_rows_syntax, appendSolved] using h8

def invBody : Peano.Formula :=
  FOL.existsAt 3 (FOL.existsAt 4
    ((mul (.var 10) (.var 3)).equal
      (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2))))))
def future : Peano.Formula := FOL.allAt 2 ((((less (.var 2) endIndex).not) ⊓
  less (.var 2) endIndex).imp invBody)
def output : Peano.Formula := FOL.existsAt 1 ((less traceBound (.var 1)) ⊓
  FOL.existsAt 10 (FOL.existsAt 9
    ((rowsAt appendRelation endIndex 9 ⊓ factorsAt endIndex 10) ⊓ future)))

private theorem sa (φ : Peano.Formula) (x y : Nat) (t : Peano.Term)
    (hxy : y ≠ x) (ht : y ∉ t.varFinset) :
    FOL.substAt (FOL.allAt y φ) x t = FOL.allAt y (FOL.substAt φ x t) := by
  unfold FOL.substAt
  apply PeanoBetaCRTAlignment.arbitrary_subst_all_at _ y
  · simp [hxy]
  · intro z hz
    by_cases h : z = x
    · simp [h, ht]
    · simp [h, Ne.symm hz]

private theorem se (φ : Peano.Formula) (x y : Nat) (t : Peano.Term)
    (hxy : y ≠ x) (ht : y ∉ t.varFinset) :
    FOL.substAt (FOL.existsAt y φ) x t = FOL.existsAt y (FOL.substAt φ x t) := by
  unfold FOL.substAt
  apply PeanoBetaCRTAlignment.arbitrary_subst_exists_at _ y
  · simp [hxy]
  · intro z hz
    by_cases h : z = x
    · simp [h, ht]
    · simp [h, Ne.symm hz]

private theorem s_and (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ ⊓ ψ) x t = (FOL.substAt φ x t) ⊓ (FOL.substAt ψ x t) := rfl
private theorem s_imp (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ.imp ψ) x t = (FOL.substAt φ x t).imp (FOL.substAt ψ x t) := rfl
private theorem s_not (φ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt φ.not x t = (FOL.substAt φ x t).not := rfl

private theorem inv_fresh : 16 ∉ (invariantAt appendRelation (.var 8)).freeVarFinset := by decide
private theorem rel_fresh : 8 ∉ appendRelation.freeVarFinset := by decide
private theorem row_fresh : 8 ∉ (beta (.var 9) (.var 1) (.var 2) (.var 3)).freeVarFinset := by decide
private theorem fact_fresh : 8 ∉ (PeanoDivisibility.divides (modulus (.var 1) (.var 2)) (.var 10)).freeVarFinset := by decide
private theorem body_fresh : 8 ∉ invBody.freeVarFinset := by decide
private theorem b_fresh : 8 ∉ (less traceBound (.var 1)).freeVarFinset := by decide
private theorem lt8 : FOL.substAt (less (.var 2) (.var 8)) 8 endIndex = less (.var 2) endIndex := by
  simp [FOL.substAt, less_subst, FirstOrder.Language.Term.subst]

private theorem rows_sub : FOL.substAt (rowsAt appendRelation (.var 8) 9) 8 endIndex = rowsAt appendRelation endIndex 9 := by
  unfold rowsAt
  rw [sa _ 8 2 _ (by decide) (by decide), s_imp, lt8, se _ 8 3 _ (by decide) (by decide), s_and,
    PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh _ _ _ rel_fresh,
    PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh _ _ _ row_fresh]

private theorem factors_sub : FOL.substAt (factorsAt (.var 8) 10) 8 endIndex = factorsAt endIndex 10 := by
  unfold factorsAt
  rw [sa _ 8 2 _ (by decide) (by decide), s_imp, lt8,
    PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh _ _ _ fact_fresh]

private theorem future_sub : FOL.substAt (futureAt (.var 8) 10) 8 endIndex = future := by
  change FOL.substAt (FOL.allAt 2 ((((less (.var 2) (.var 8)).not) ⊓
      less (.var 2) (.var 8)).imp invBody)) 8 endIndex = future
  unfold future
  rw [sa _ 8 2 _ (by decide) (by decide), s_imp, s_and, s_not, lt8,
    PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh _ _ _ body_fresh]

theorem first_sub : FOL.substAt (boundedSolvedParameter appendRelation) 16 traceBound =
    FOL.existsAt 1 ((less traceBound (.var 1)) ⊓ invariantAt appendRelation (.var 8)) := by
  unfold boundedSolvedParameter
  rw [se _ 16 1 _ (by decide) (by decide), s_and,
    PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh _ _ _ inv_fresh]
  congr 2
  simp [FOL.substAt, less_subst, FirstOrder.Language.Term.subst]

theorem second_sub : FOL.substAt
    (FOL.existsAt 1 ((less traceBound (.var 1)) ⊓ invariantAt appendRelation (.var 8))) 8 endIndex = output := by
  unfold output invariantAt invariantWith matrixAt
  rw [se _ 8 1 _ (by decide) (by decide), s_and,
    PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh _ _ _ b_fresh,
    se _ 8 10 _ (by decide) (by decide), se _ 8 9 _ (by decide) (by decide),
    s_and, s_and, rows_sub, factors_sub, future_sub]

/-- The specialized result is the displayed code/product invariant, with
both occurrences of the outer index bound replaced. -/
theorem solved_syntax : appendSolved = output := by
  unfold appendSolved
  rw [← specialization_syntax, first_sub, second_sub]

/-- PA constructs a new code and parameter realizing all desired append rows,
with a product certificate and the displayed larger-parameter bound. This does
not yet transfer the old power-trace transitions. -/
theorem append_crt_exists : FormulaProves output := by
  have hrows : FormulaProves boundedAppendRows := by
    simpa only [boundedAppendRows, endIndex, traceBound,
      PeanoBetaAppendBound.traceBound] using PeanoBetaAppendBound.bounded_append_rows
  have hs := FOL.Derivation.mp bounded_append_solve hrows
  rwa [solved_syntax] at hs


end PASoundness.PeanoBetaAppendCRT
