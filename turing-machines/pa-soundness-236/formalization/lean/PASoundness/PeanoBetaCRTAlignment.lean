import PASoundness.PeanoBetaCRTRecordMerge
import PASoundness.PeanoBetaCRTInvariant

/-! Capture-safe named-variable alignment for the fixed CRT record step and
its invariant interface. Freshness and update premises remain explicit; this
module does not itself assert a CRT induction or trace existence. -/
namespace PASoundness.PeanoBetaCRTAlignment
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic
open PeanoBetaCRTRecordStep

/-- Move source state/witness names to the invariant layout. Four temporary
source names restore target parameters that would otherwise be overwritten. -/
def align (x : Nat) : Peano.Term :=
  if x = 0 then .var 9 else if x = 4 then .var 10 else if x = 6 then .var 7
  else if x = 8 then .var 13 else if x = 9 then .var 14 else if x = 10 then .var 15
  else if x = 16 then .var 0 else if x = 17 then .var 4 else if x = 18 then .var 6
  else if x = 19 then .var 8 else .var x

/-- Preserve target predicate parameters 0,4,6,8 in temporary source names. -/
def lift (x : Nat) : Peano.Term :=
  if x = 0 then .var 16 else if x = 4 then .var 17 else if x = 6 then .var 18
  else if x = 8 then .var 19 else .var x

def lifted (φ : Peano.Formula) : Peano.Formula := φ.subst lift

/-- If the target parameter formula avoids the source witness names 9,10 and
fresh placeholders 16 through 19, lifting then renaming restores it exactly.
It may freely contain the state names 0,4,6,8, which are restored. -/
theorem lift_align_identity (φ : Peano.Formula)
    (h9 : 9 ∉ φ.freeVarFinset) (h10 : 10 ∉ φ.freeVarFinset)
    (h16 : 16 ∉ φ.freeVarFinset) (h17 : 17 ∉ φ.freeVarFinset)
    (h18 : 18 ∉ φ.freeVarFinset) (h19 : 19 ∉ φ.freeVarFinset) :
    (φ.subst lift).subst align = φ := by
  rw [SyntaxTransport.formula_subst_comp]
  calc
    φ.subst (fun x => (lift x).subst align) = φ.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro x hx
      have hx9 : x ≠ 9 := by intro h; subst x; exact h9 hx
      have hx10 : x ≠ 10 := by intro h; subst x; exact h10 hx
      have hx16 : x ≠ 16 := by intro h; subst x; exact h16 hx
      have hx17 : x ≠ 17 := by intro h; subst x; exact h17 hx
      have hx18 : x ≠ 18 := by intro h; subst x; exact h18 hx
      have hx19 : x ≠ 19 := by intro h; subst x; exact h19 hx
      by_cases hx0 : x = 0
      · subst x; rfl
      by_cases hx4 : x = 4
      · subst x; rfl
      by_cases hx6 : x = 6
      · subst x; rfl
      by_cases hx8 : x = 8
      · subst x; rfl
      simp [lift, align, hx0, hx4, hx6, hx8, hx9, hx10,
        hx16, hx17, hx18, hx19, FirstOrder.Language.Term.subst]
    _ = φ := SyntaxTransport.formula_subst_var φ


/-- Target code/product/bound and witness names are reserved for the update;
the four temporary names must also be fresh in the desired-row relation. -/
def reservedNames : List Nat := [7,9,10,11,12,13,14,15,16,17,18,19]

def NamesSafe (φ : Peano.Formula) : Prop :=
  ∀ x ∈ φ.freeVarFinset, x ∉ reservedNames


def substName (src dst : Nat) : Nat → Peano.Term :=
  fun x => if x = src then .var dst else .var x

/-- A single safe capture-avoiding substitution uses proof generalization and
universal elimination. No substitution-closure premise on PA axioms is used. -/
theorem specialize (φ : Peano.Formula) (src dst : Nat) (h : FormulaProves φ) :
    FormulaProves (φ.subst (substName src dst)) := by
  exact .mp (.logical (.allElim φ src (.var dst))) (.generalize src h)

/-- Sequential specialization computes the intended simultaneous map. The
last four steps restore independent placeholder parameters 16,17,18,19. -/
theorem align_equation (φ : Peano.Formula) :
    ((((((((((φ.subst (substName 9 14)).subst (substName 10 15)).subst (substName 8 13)).subst
        (substName 6 7)).subst (substName 4 10)).subst (substName 0 9)).subst
        (substName 16 0)).subst (substName 17 4)).subst (substName 18 6)).subst
        (substName 19 8)) = φ.subst align := by
  simp only [SyntaxTransport.formula_subst_comp]
  congr 1
  funext x
  by_cases h0 : x = 0
  · subst x; rfl
  by_cases h4 : x = 4
  · subst x; rfl
  by_cases h6 : x = 6
  · subst x; rfl
  by_cases h8 : x = 8
  · subst x; rfl
  by_cases h9 : x = 9
  · subst x; rfl
  by_cases h10 : x = 10
  · subst x; rfl
  by_cases h16 : x = 16
  · subst x; rfl
  by_cases h17 : x = 17
  · subst x; rfl
  by_cases h18 : x = 18
  · subst x; rfl
  by_cases h19 : x = 19
  · subst x; rfl
  simp [align, substName, h0, h4, h6, h8, h9, h10, h16, h17, h18, h19,
    FirstOrder.Language.Term.subst]

/-- Derive the concrete simultaneous renaming on an arbitrary PA theorem. -/
theorem align_proves (φ : Peano.Formula) (h : FormulaProves φ) :
    FormulaProves (φ.subst align) := by
  have h1 := specialize φ 9 14 h
  have h2 := specialize _ 10 15 h1
  have h3 := specialize _ 8 13 h2
  have h4 := specialize _ 6 7 h3
  have h5 := specialize _ 4 10 h4
  have h6 := specialize _ 0 9 h5
  have h7 := specialize _ 16 0 h6
  have h8 := specialize _ 17 4 h7
  have h9 := specialize _ 18 6 h8
  have h10 := specialize _ 19 8 h9
  rw [align_equation] at h10
  exact h10

/-- The entire one-step PA derivation is transported through the concrete
name map by ten actual generalization/elimination steps. The result is still
written as an explicit syntactic substitution; later lemmas normalize its
predicate and quantifier clauses. -/
theorem aligned_record_derivation (φ : Peano.Formula) :
    FormulaProves
      ((PeanoBetaUniformPreserve.boundedDivisors.imp
        ((oldFamily (lifted φ)).imp ((selected (lifted φ)).imp
          (certificate.imp (selectedBound.imp
            (PeanoBetaCRTRecordMerge.fullNewFamily (lifted φ))))))).subst align) :=
  align_proves _ (PeanoBetaCRTRecordMerge.full_record_step (lifted φ))

def targetSelected (φ : Peano.Formula) : Peano.Formula :=
  φ.subst (fun x => if x=2 then .var 7 else if x=3 then .var 13 else .var x)


theorem round_trip (φ : Peano.Formula)
    (hf : ∀ x ∈ φ.freeVarFinset, x ∉ reservedNames) : (lifted φ).subst align = φ := by
  unfold lifted
  rw [SyntaxTransport.formula_subst_comp]
  calc
    _ = φ.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro x hx
      have h := hf x hx
      simp only [reservedNames, List.mem_cons, not_or] at h
      simp only [lift]
      split_ifs <;> simp_all [FirstOrder.Language.Term.subst, align]
    _ = φ := SyntaxTransport.formula_subst_var _

theorem selected_commutes (φ : Peano.Formula)
    (hf : ∀ x ∈ φ.freeVarFinset, x ∉ reservedNames) :
    (selected (lifted φ)).subst align = targetSelected φ := by
  unfold selected lifted targetSelected
  repeat rw [SyntaxTransport.formula_subst_comp]
  apply SyntaxTransport.formula_subst_agree
  intro x hx
  have h := hf x hx
  simp only [reservedNames, List.mem_cons, not_or] at h
  simp only [lift]
  split_ifs <;> simp_all [FirstOrder.Language.Term.subst, align]


def binderRenameName (x : Nat) : Nat :=
  if x=0 then 9 else if x=4 then 10 else if x=6 then 7 else
  if x=8 then 13 else if x=9 then 14 else if x=10 then 15 else
  if x=16 then 0 else if x=17 then 4 else if x=18 then 6 else
  if x=19 then 8 else x

def binderRename (x : Nat) : Peano.Term := .var (binderRenameName x)

theorem binder_rename_eq_two (x : Nat) : binderRenameName x = 2 ↔ x = 2 := by
  unfold binderRenameName
  split_ifs <;> simp_all

theorem binder_rename_eq_three (x : Nat) : binderRenameName x = 3 ↔ x = 3 := by
  unfold binderRenameName
  split_ifs <;> simp_all

def binder (b x : Nat) : Nat ⊕ Fin 1 := if x=b then .inr 0 else .inl x

theorem binder_term_comm (b : Nat) (hfix : binderRenameName b = b)
    (hequiv : ∀ x, binderRenameName x = b ↔ x = b) {n : Nat} (t : Peano.language.Term (Nat ⊕ Fin n)) :
    (t.relabel (BoundedFormula.relabelAux (binder b) n)).subst
        (SyntaxTransport.liftSub (1+n) binderRename) =
      (t.subst (SyntaxTransport.liftSub n binderRename)).relabel
        (BoundedFormula.relabelAux (binder b) n) := by
  rw [SyntaxTransport.term_relabel_subst, SyntaxTransport.term_subst_relabel]
  congr 1
  funext x
  cases x with
  | inl x =>
      by_cases hx : x = b
      · subst x
        simp [SyntaxTransport.liftSub, BoundedFormula.relabelAux, binder, binderRename, hfix,
          Term.relabel]
      · have hr : binderRenameName x ≠ b := fun h => hx ((hequiv x).mp h)
        simp [SyntaxTransport.liftSub, BoundedFormula.relabelAux, binder, binderRename, hx, hr,
          Term.relabel]
  | inr x =>
      simp [SyntaxTransport.liftSub, BoundedFormula.relabelAux, Term.relabel]

theorem binder_comm (b : Nat) (hfix : binderRenameName b = b)
    (hequiv : ∀ x, binderRenameName x = b ↔ x = b) {n : Nat}
    (R : Peano.language.BoundedFormula Nat n) :
    (R.relabel (binder b)).subst binderRename = (R.subst binderRename).relabel (binder b) := by
  induction R with
  | falsum => rfl
  | equal t u =>
      simp only [FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.subst,
        FirstOrder.Language.BoundedFormula.mapTermRel]
      congr 1 <;> exact binder_term_comm b hfix hequiv _
  | rel r ts =>
      simp only [FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.subst,
        FirstOrder.Language.BoundedFormula.mapTermRel]
      congr 1
      funext i
      exact binder_term_comm b hfix hequiv _
  | imp a b ia ib =>
      simp only [FirstOrder.Language.BoundedFormula.relabel_imp, FirstOrder.Language.BoundedFormula.subst,
        FirstOrder.Language.BoundedFormula.mapTermRel] at *
      rw [ia, ib]
  | all f ih =>
      simp only [FirstOrder.Language.BoundedFormula.relabel_all, FirstOrder.Language.BoundedFormula.subst,
        FirstOrder.Language.BoundedFormula.mapTermRel] at *
      simpa only [id_eq] using congrArg BoundedFormula.all ih

theorem align_all_at (b : Nat) (hfix : binderRenameName b = b)
    (hequiv : ∀ x, binderRenameName x = b ↔ x = b) (R : Peano.Formula) :
    (FOL.allAt b R).subst binderRename = FOL.allAt b (R.subst binderRename) := by
  unfold FOL.allAt
  simp only [BoundedFormula.subst, BoundedFormula.mapTermRel]
  exact congrArg BoundedFormula.all (binder_comm b hfix hequiv R)

theorem align_exists_at (b : Nat) (hfix : binderRenameName b = b)
    (hequiv : ∀ x, binderRenameName x = b ↔ x = b) (R : Peano.Formula) :
    (FOL.existsAt b R).subst binderRename = FOL.existsAt b (R.subst binderRename) := by
  have subst_not (φ : Peano.Formula) : φ.not.subst binderRename = (φ.subst binderRename).not := by
    simp [BoundedFormula.not, BoundedFormula.subst, BoundedFormula.mapTermRel]
    rfl
  unfold FOL.existsAt
  rw [subst_not, align_all_at b hfix hequiv, subst_not]

theorem all_two (R : Peano.Formula) :
    (FOL.allAt 2 R).subst binderRename = FOL.allAt 2 (R.subst binderRename) :=
  align_all_at 2 (by decide) binder_rename_eq_two R

theorem exists_three (R : Peano.Formula) :
    (FOL.existsAt 3 R).subst binderRename = FOL.existsAt 3 (R.subst binderRename) :=
  align_exists_at 3 (by decide) binder_rename_eq_three R


/-- The term-valued alignment is exactly the variable renaming used in the
binder-commutation proof below. -/
theorem binderRename_eq_align : binderRename = align := by
  funext x
  unfold binderRename binderRenameName align
  split_ifs <;> rfl

/-- Alignment commutes syntactically with the fixed row-index and row-value
binders, because no other free name is mapped to 2 or 3. -/
theorem align_all_two (R : Peano.Formula) :
    (FOL.allAt 2 R).subst align = FOL.allAt 2 (R.subst align) := by
  simpa only [binderRename_eq_align] using all_two R

theorem align_exists_three (R : Peano.Formula) :
    (FOL.existsAt 3 R).subst align = FOL.existsAt 3 (R.subst align) := by
  simpa only [binderRename_eq_align] using exists_three R

private theorem term_relabel_agree {α β : Type} [DecidableEq α]
    (t : Peano.language.Term α) (r s : α → β)
    (h : ∀ x ∈ t.varFinset, r x = s x) : t.relabel r = t.relabel s := by
  induction t with
  | var x => exact congrArg Term.var (h x (by simp [Term.varFinset]))
  | func f ts ih =>
    simp only [Term.relabel]
    congr 1
    funext i
    apply ih i
    intro x hx
    apply h x
    simp only [Term.varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, hx⟩

theorem term_bind_fresh {n : Nat} (b : Nat) (t : Peano.Term) (h : b ∉ t.varFinset) :
    (t.relabel Sum.inl).relabel (BoundedFormula.relabelAux (binder b) n) =
      t.relabel (Sum.inl : Nat → Nat ⊕ Fin (1+n)) := by
  rw [Term.relabel_relabel]
  apply term_relabel_agree
  intro x hx
  have hne : x ≠ b := by intro he; subst x; exact h hx
  simp [binder, BoundedFormula.relabelAux, hne]


theorem arbitrary_term_comm (σ : Nat → Peano.Term) (b : Nat) (hfix : σ b = .var b)
    (havoid : ∀ x, x ≠ b → b ∉ (σ x).varFinset)
    {n : Nat} (t : Peano.language.Term (Nat ⊕ Fin n)) :
    (t.relabel (BoundedFormula.relabelAux (binder b) n)).subst
        (SyntaxTransport.liftSub (1+n) σ) =
      (t.subst (SyntaxTransport.liftSub n σ)).relabel
        (BoundedFormula.relabelAux (binder b) n) := by
  rw [SyntaxTransport.term_relabel_subst, SyntaxTransport.term_subst_relabel]
  congr 1
  funext x
  cases x with
  | inl x =>
      by_cases hx : x = b
      · subst x
        simp [SyntaxTransport.liftSub, BoundedFormula.relabelAux, binder, hfix,
          Term.relabel]
      · simp only [SyntaxTransport.liftSub, Sum.elim_inl, Function.comp_apply]
        have hbind : BoundedFormula.relabelAux (binder b) n (.inl x) = .inl x := by
          simp [BoundedFormula.relabelAux, binder, hx]
        rw [hbind]
        simp only [Sum.elim_inl, Function.comp_apply]
        exact (term_bind_fresh b (σ x) (havoid x hx)).symm
  | inr x =>
      simp [SyntaxTransport.liftSub, BoundedFormula.relabelAux, Term.relabel]

theorem arbitrary_binder_comm (σ : Nat → Peano.Term) (b : Nat) (hfix : σ b = .var b)
    (havoid : ∀ x, x ≠ b → b ∉ (σ x).varFinset) {n : Nat}
    (R : Peano.language.BoundedFormula Nat n) :
    (R.relabel (binder b)).subst σ = (R.subst σ).relabel (binder b) := by
  induction R with
  | falsum => rfl
  | equal t u =>
      simp only [FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.subst,
        FirstOrder.Language.BoundedFormula.mapTermRel]
      congr 1 <;> exact arbitrary_term_comm σ b hfix havoid _
  | rel r ts =>
      simp only [FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.subst,
        FirstOrder.Language.BoundedFormula.mapTermRel]
      congr 1
      funext i
      exact arbitrary_term_comm σ b hfix havoid _
  | imp a b ia ib =>
      simp only [FirstOrder.Language.BoundedFormula.relabel_imp, FirstOrder.Language.BoundedFormula.subst,
        FirstOrder.Language.BoundedFormula.mapTermRel] at *
      rw [ia, ib]
  | all f ih =>
      simp only [FirstOrder.Language.BoundedFormula.relabel_all, FirstOrder.Language.BoundedFormula.subst,
        FirstOrder.Language.BoundedFormula.mapTermRel] at *
      simpa only [id_eq] using congrArg BoundedFormula.all ih

theorem arbitrary_subst_all_at (σ : Nat → Peano.Term) (b : Nat) (hfix : σ b = .var b)
    (havoid : ∀ x, x ≠ b → b ∉ (σ x).varFinset) (R : Peano.Formula) :
    (FOL.allAt b R).subst σ = FOL.allAt b (R.subst σ) := by
  unfold FOL.allAt
  simp only [BoundedFormula.subst, BoundedFormula.mapTermRel]
  exact congrArg BoundedFormula.all (arbitrary_binder_comm σ b hfix havoid R)

theorem arbitrary_subst_exists_at (σ : Nat → Peano.Term) (b : Nat) (hfix : σ b = .var b)
    (havoid : ∀ x, x ≠ b → b ∉ (σ x).varFinset) (R : Peano.Formula) :
    (FOL.existsAt b R).subst σ = FOL.existsAt b (R.subst σ) := by
  have subst_not (φ : Peano.Formula) : φ.not.subst σ = (φ.subst σ).not := by
    simp [BoundedFormula.not, BoundedFormula.subst, BoundedFormula.mapTermRel]
    rfl
  unfold FOL.existsAt
  rw [subst_not, arbitrary_subst_all_at σ b hfix havoid, subst_not]


/-- Substitution of the output-code name 11 passes the index binder 2
when the inserted term does not contain that bound name. -/
theorem all_two_subst11 (R : Peano.Formula) (t : Peano.Term) (ht : 2 ∉ t.varFinset) :
    FOL.substAt (FOL.allAt 2 R) 11 t = FOL.allAt 2 (FOL.substAt R 11 t) := by
  unfold FOL.substAt
  apply arbitrary_subst_all_at (fun x => if x = 11 then t else .var x) 2
  · simp
  · intro x hx
    by_cases he : x = 11
    · subst x; simpa using ht
    · simp [he, Ne.symm hx]

/-- The same substitution passes the row-witness binder 3 when the inserted
term is fresh for name 3. -/
theorem exists_three_subst11 (R : Peano.Formula) (t : Peano.Term) (ht : 3 ∉ t.varFinset) :
    FOL.substAt (FOL.existsAt 3 R) 11 t = FOL.existsAt 3 (FOL.substAt R 11 t) := by
  unfold FOL.substAt
  apply arbitrary_subst_exists_at (fun x => if x = 11 then t else .var x) 3
  · simp
  · intro x hx
    by_cases he : x = 11
    · subst x; simpa using ht
    · simp [he, Ne.symm hx]


/-- The concrete increment in invariant names: B=9, C=1, P=10, k=7,
selected value=13, inverse witness=14. -/
def alignedIncrement : Peano.Term :=
  mul (.var 10) (mul (.var 14)
    (add (.var 13) (mul (mul (succ (.var 7)) (.var 1)) (.var 9))))

def alignedCode : Peano.Term := add (.var 9) alignedIncrement

def alignedProduct : Peano.Term := mul (.var 10) (modulus (.var 1) (.var 7))

/-- The record-step increment becomes exactly the intended new increment. -/
theorem increment_alignment : increment.subst align = alignedIncrement := by
  simp [increment, alignedIncrement, align, mul_subst, add_subst, succ_subst,
    FirstOrder.Language.Term.subst]

/-- The updated code matches the invariant's B witness term. -/
theorem code_alignment : updatedCode.subst align = alignedCode := by
  simp [updatedCode, alignedCode, increment_alignment, align, add_subst,
    FirstOrder.Language.Term.subst]

/-- The PA inverse-certificate equation is aligned without a semantic step. -/
theorem certificate_alignment : certificate.subst align =
    ((mul (.var 10) (.var 14)).equal
      (add (succ zero) (mul (.var 15) (modulus (.var 1) (.var 7))))) := by
  simp [certificate, align, FOL.equality_subst, mul_subst, add_subst, succ_subst,
    modulus, PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst]

/-- The selected-value bound is aligned with the same current modulus. -/
theorem selected_bound_alignment : selectedBound.subst align =
    less (.var 13) (modulus (.var 1) (.var 7)) := by
  simp [selectedBound, align, CompactArithmetic.less_subst, modulus, mul_subst, succ_subst,
    FirstOrder.Language.Term.subst]

/-- The selected beta row uses the exact aligned code, parameter and boundary. -/
theorem selected_beta_alignment : selectedBeta.subst align =
    beta alignedCode (.var 1) (.var 7) (.var 13) := by
  simp [selectedBeta, beta_subst, code_alignment, align, FirstOrder.Language.Term.subst]

/-- The old and updated row matrices align with the invariant's code name 9
and the same bound index/value names 2 and 3. -/
theorem old_row_alignment : PeanoBetaUniformPreserve.oldRow.subst align =
    beta (.var 9) (.var 1) (.var 2) (.var 3) := by
  simp [PeanoBetaUniformPreserve.oldRow, beta_subst, align, FirstOrder.Language.Term.subst]

theorem updated_row_alignment : updatedRow.subst align =
    beta alignedCode (.var 1) (.var 2) (.var 3) := by
  simp [updatedRow, beta_subst, code_alignment, align, FirstOrder.Language.Term.subst]

/-- The bounded divisor premise becomes the invariant's factors clause. -/
theorem factors_alignment : PeanoBetaUniformPreserve.boundedDivisors.subst align =
    PeanoBetaCRTInvariant.factorsAt (.var 7) 10 := by
  simp [PeanoBetaUniformPreserve.boundedDivisors, PeanoBetaCRTInvariant.factorsAt,
    PeanoDivisibility.divides, PeanoDivisibility.dividesTemplate, align,
    FOL.existsAt, FOL.allAt, CompactArithmetic.less, CompactArithmetic.lessTemplate,
    CompactArithmetic.exAt, CompactArithmetic.modulus, CompactArithmetic.v,
    Peano.add, Peano.mul, Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst,
    FirstOrder.Language.Term.relabel, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.subst, FirstOrder.Language.BoundedFormula.relabel,
    FirstOrder.Language.BoundedFormula.mapTermRel, FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])


private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not, subst_imp, subst_not]

/-- The transported old row family is exactly the invariant's current rows. -/
theorem old_family_alignment (φ : Peano.Formula) (hφ : NamesSafe φ) :
    (oldFamily (lifted φ)).subst align = PeanoBetaCRTInvariant.rowsAt φ (.var 7) 9 := by
  simp only [oldFamily, oldExists, PeanoBetaCRTRecordStep.bound,
    PeanoBetaCRTInvariant.rowsAt, align_all_two, subst_imp, align_exists_three,
    subst_and, round_trip φ hφ, old_row_alignment, CompactArithmetic.less_subst,
    FirstOrder.Language.Term.subst, align, ↓reduceIte]
  simp

/-- Updated rows in the invariant's free-name layout, before replacement of the
fresh output witness name in `nextRows`. -/
def alignedRows (φ : Peano.Formula) : Peano.Formula :=
  FOL.allAt 2 ((less (.var 2) (succ (.var 7))).imp
    (FOL.existsAt 3 (φ ⊓ beta alignedCode (.var 1) (.var 2) (.var 3))))

/-- The transported updated row family has the exact displayed syntax. -/
theorem new_family_alignment (φ : Peano.Formula) (hφ : NamesSafe φ) :
    (PeanoBetaCRTRecordMerge.fullNewFamily (lifted φ)).subst align = alignedRows φ := by
  simp only [PeanoBetaCRTRecordMerge.fullNewFamily, newExists, alignedRows,
    align_all_two, subst_imp, align_exists_three, subst_and, round_trip φ hφ,
    updated_row_alignment, CompactArithmetic.less_subst, succ_subst,
    FirstOrder.Language.Term.subst, align, ↓reduceIte]
  simp

/-- Aligned PA derivation with the divisor, selected predicate, inverse
certificate and selected bound normalized. The old and new quantified family
clauses remain explicitly substituted; later lemmas normalize them. -/
theorem partially_aligned_record_step (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FormulaProves
      ((PeanoBetaCRTInvariant.factorsAt (.var 7) 10).imp
        (((oldFamily (lifted φ)).subst align).imp ((targetSelected φ).imp
          (((mul (.var 10) (.var 14)).equal
            (add (succ zero) (mul (.var 15) (modulus (.var 1) (.var 7))))).imp
              ((less (.var 13) (modulus (.var 1) (.var 7))).imp
                ((PeanoBetaCRTRecordMerge.fullNewFamily (lifted φ)).subst align)))))) := by
  have h := aligned_record_derivation φ
  simpa only [subst_imp, factors_alignment, selected_commutes φ hφ,
    certificate_alignment, selected_bound_alignment] using h

/-- The exact row update in the invariant's named state, with a single explicit
selected value and inverse certificate. The target is `alignedRows`; the later
`nextRows_both_alignment` lemma identifies it with the invariant interface. -/
theorem aligned_record_step (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FormulaProves
      ((PeanoBetaCRTInvariant.factorsAt (.var 7) 10).imp
        ((PeanoBetaCRTInvariant.rowsAt φ (.var 7) 9).imp ((targetSelected φ).imp
          (((mul (.var 10) (.var 14)).equal
            (add (succ zero) (mul (.var 15) (modulus (.var 1) (.var 7))))).imp
              ((less (.var 13) (modulus (.var 1) (.var 7))).imp (alignedRows φ)))))) := by
  have h := partially_aligned_record_step φ hφ
  simpa only [old_family_alignment φ hφ, new_family_alignment φ hφ] using h

/-- A substitution at a name absent from a formula has no effect. This is a
syntactic identity, independent of PA soundness. -/
theorem substAt_fresh (ψ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (hx : x ∉ ψ.freeVarFinset) : FOL.substAt ψ x t = ψ := by
  unfold FOL.substAt
  calc
    ψ.subst (fun y => if y = x then t else .var y) = ψ.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      have hne : y ≠ x := by intro h; subst y; exact hx hy
      simp [hne]
    _ = ψ := SyntaxTransport.formula_subst_var ψ

/-- The updated row family does not use output product name 12. -/
theorem alignedRows_fresh12 (φ : Peano.Formula) (hφ : NamesSafe φ) :
    12 ∉ (alignedRows φ).freeVarFinset := by
  have hφ12 : 12 ∉ φ.freeVarFinset := by
    intro hm
    have hh := hφ 12 hm
    simp [reservedNames] at hh
  have hb : 12 ∉ (beta alignedCode (.var 1) (.var 2) (.var 3)).freeVarFinset := by decide
  have hc : 12 ∉ (less (.var 2) (succ (.var 7))).freeVarFinset := by decide
  have hconj : 12 ∉ (φ ⊓ beta alignedCode (.var 1) (.var 2) (.var 3)).freeVarFinset := by
    change 12 ∉ (φ.imp (beta alignedCode (.var 1) (.var 2) (.var 3)).not).not.freeVarFinset
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hφ12, hb]
  simp [alignedRows, FOL.existsAt, SyntaxTransport.allAt_freeVars,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset,
    hconj, hc]

private theorem substAt_imp (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ.imp ψ) x t = (FOL.substAt φ x t).imp (FOL.substAt ψ x t) := rfl

private theorem substAt_and (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ ⊓ ψ) x t = (FOL.substAt φ x t) ⊓ (FOL.substAt ψ x t) := rfl

/-- Substituting the explicit new-code term into the invariant's next-row
clause yields the aligned updated family exactly. -/
theorem nextRows_code_alignment (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FOL.substAt (PeanoBetaCRTInvariant.nextRows φ) 11 alignedCode = alignedRows φ := by
  have hφ11 : 11 ∉ φ.freeVarFinset := by
    intro hm
    have hh := hφ 11 hm
    simp [reservedNames] at hh
  have h2 : 2 ∉ alignedCode.varFinset := by decide
  have h3 : 3 ∉ alignedCode.varFinset := by decide
  have hg : FOL.substAt (less (.var 2) (succ (.var 7))) 11 alignedCode =
      less (.var 2) (succ (.var 7)) :=
    substAt_fresh _ _ _ (by decide)
  have hb : FOL.substAt (beta (.var 11) (.var 1) (.var 2) (.var 3)) 11 alignedCode =
      beta alignedCode (.var 1) (.var 2) (.var 3) := by
    simp [FOL.substAt, beta_subst, FirstOrder.Language.Term.subst]
  unfold PeanoBetaCRTInvariant.nextRows PeanoBetaCRTInvariant.rowsAt alignedRows
  rw [all_two_subst11 _ _ h2, substAt_imp, hg, exists_three_subst11 _ _ h3,
    substAt_and, substAt_fresh φ 11 alignedCode hφ11, hb]

/-- Both output substitutions used by `conditional_successor` reduce to the
same aligned row family. The product witness is absent from the row clause. -/
theorem nextRows_both_alignment (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FOL.substAt (FOL.substAt (PeanoBetaCRTInvariant.nextRows φ) 11 alignedCode)
      12 alignedProduct = alignedRows φ := by
  rw [nextRows_code_alignment φ hφ]
  exact substAt_fresh _ _ _ (alignedRows_fresh12 φ hφ)

/-- Selected value, inverse certificate and bound, packaged as one explicit
side condition in the invariant's named state. -/
def rowAssumptions (φ : Peano.Formula) : Peano.Formula :=
  ((targetSelected φ) ⊓
    ((mul (.var 10) (.var 14)).equal
      (add (succ zero) (mul (.var 15) (modulus (.var 1) (.var 7)))))) ⊓
    less (.var 13) (modulus (.var 1) (.var 7))

/-- The row component of the current invariant and the stated selected-value
side condition imply the updated row family in aligned syntax. -/
theorem rows_component_aligned (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FormulaProves ((rowAssumptions φ).imp
      ((PeanoBetaCRTInvariant.currentMatrix φ).imp (alignedRows φ))) := by
  let A := rowAssumptions φ
  let C := PeanoBetaCRTInvariant.currentMatrix φ
  let Γ := [C,A]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have ha : FOL.Context Peano.Axiom Γ A := FOL.Context.under (FOL.Context.head [] A) C
  have hc : FOL.Context Peano.Axiom Γ C := FOL.Context.head _ _
  have hsel := FOL.Context.conjunctionLeft (FOL.Context.conjunctionLeft ha)
  have hcert := FOL.Context.conjunctionRight (FOL.Context.conjunctionLeft ha)
  have hbd := FOL.Context.conjunctionRight ha
  have hrows := FOL.Context.conjunctionLeft (FOL.Context.conjunctionLeft hc)
  have hdiv := FOL.Context.conjunctionRight (FOL.Context.conjunctionLeft hc)
  exact .mp (.mp (.mp (.mp (.mp (.closed (aligned_record_step φ hφ)) hdiv) hrows) hsel) hcert) hbd

/-- The same row component in the exact double-substitution interface expected
by the conditional successor wrapper. The side condition still refers to the
current product and selected witnesses, and is not asserted as an outer
assumption fresh of the old existential witnesses. -/
theorem rows_component_exact (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FormulaProves ((rowAssumptions φ).imp
      ((PeanoBetaCRTInvariant.currentMatrix φ).imp
        (FOL.substAt (FOL.substAt (PeanoBetaCRTInvariant.nextRows φ) 11 alignedCode)
          12 alignedProduct))) := by
  rw [nextRows_both_alignment φ hφ]
  exact rows_component_aligned φ hφ

end PASoundness.PeanoBetaCRTAlignment
