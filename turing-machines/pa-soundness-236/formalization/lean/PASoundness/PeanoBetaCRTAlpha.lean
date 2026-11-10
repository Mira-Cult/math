import PASoundness.PeanoBetaCRTInvariant

/-! Derivational alpha-renaming for the existential code/product witnesses in
the bounded CRT invariant. This neither proves the update hypotheses nor the
CRT induction step. -/
namespace PASoundness.PeanoBetaCRTAlpha
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoDivisibility
open PeanoBetaCRTInvariant

/-- Replacing free x by fresh y and then y by x recovers the exact syntax. -/
theorem subst_roundtrip (φ : Peano.Formula) (x y : Nat)
    (_hxy : x ≠ y) (hy : y ∉ φ.freeVarFinset) :
    FOL.substAt (FOL.substAt φ x (.var y)) y (.var x) = φ := by
  unfold FOL.substAt
  rw [SyntaxTransport.formula_subst_comp]
  calc
    φ.subst (fun a => (if a = x then (.var y : Peano.Term) else .var a).subst
      (fun z => if z = y then (.var x : Peano.Term) else .var z)) = φ.subst Term.var := by
        apply SyntaxTransport.formula_subst_agree
        intro a ha
        have hay : a ≠ y := by intro h; subst a; exact hy ha
        by_cases hax : a = x
        · subst a
          simp [FirstOrder.Language.Term.subst]
        · simp [hax, hay, FirstOrder.Language.Term.subst]
    _ = φ := SyntaxTransport.formula_subst_var _

/-- x has been removed from the renamed formula's free-variable support. -/
theorem subst_rename_fresh (φ : Peano.Formula) (x y : Nat) (hxy : x ≠ y) :
    x ∉ (FOL.substAt φ x (.var y)).freeVarFinset := by
  unfold FOL.substAt
  rw [SyntaxTransport.formula_subst_freeVars]
  rintro ⟨z,hz,h⟩
  by_cases hz' : z = x
  · subst z
    simp [FirstOrder.Language.Term.varFinset, hxy] at h
  · have he : x = z := by simpa [hz', FirstOrder.Language.Term.varFinset] using h
    exact hz' he.symm

/-- A variable may be changed to a fresh name under an existential. This is a
syntactic PA proof transformation, not a semantic equivalence argument. -/
theorem exists_alpha_forward (φ : Peano.Formula) (x y : Nat)
    (hxy : x ≠ y) (hy : y ∉ φ.freeVarFinset) :
    FormulaProves ((FOL.existsAt x φ).imp
      (FOL.existsAt y (FOL.substAt φ x (.var y)))) := by
  let ψ := FOL.substAt φ x (.var y)
  let T := FOL.existsAt y ψ
  have hi : FormulaProves (φ.imp T) := by
    have h := FOL.Derivation.existsIntro (A := Peano.Axiom) ψ y (.var x)
    rw [show FOL.substAt ψ y (.var x) = φ from subst_roundtrip φ x y hxy hy] at h
    exact h
  have hf : x ∉ T.freeVarFinset := by
    simp only [T, FOL.existsAt, FirstOrder.Language.BoundedFormula.not,
      FirstOrder.Language.BoundedFormula.freeVarFinset, Finset.union_empty,
      SyntaxTransport.allAt_freeVars, Finset.mem_erase]
    intro h
    exact subst_rename_fresh φ x y hxy h.2
  exact PeanoBitPositionReduction.exists_elim x hf hi

/-- The reverse direction uses the same named witness; it only requires that
the new binder y is fresh for the original formula. -/
theorem exists_alpha_reverse (φ : Peano.Formula) (x y : Nat)
    (hy : y ∉ φ.freeVarFinset) :
    FormulaProves ((FOL.existsAt y (FOL.substAt φ x (.var y))).imp
      (FOL.existsAt x φ)) := by
  let ψ := FOL.substAt φ x (.var y)
  let T := FOL.existsAt x φ
  have hi : FormulaProves (ψ.imp T) :=
    FOL.Derivation.existsIntro φ x (.var y)
  have hf : y ∉ T.freeVarFinset := by
    simp only [T, FOL.existsAt, FirstOrder.Language.BoundedFormula.not,
      FirstOrder.Language.BoundedFormula.freeVarFinset, Finset.union_empty,
      SyntaxTransport.allAt_freeVars, Finset.mem_erase]
    intro h
    exact hy h.2
  exact PeanoBitPositionReduction.exists_elim y hf hi

/-- Both directions of alpha-renaming as object-level PA derivations. -/
theorem exists_alpha (φ : Peano.Formula) (x y : Nat)
    (hxy : x ≠ y) (hy : y ∉ φ.freeVarFinset) :
    FormulaProves ((FOL.existsAt x φ).imp
      (FOL.existsAt y (FOL.substAt φ x (.var y)))) ∧
    FormulaProves ((FOL.existsAt y (FOL.substAt φ x (.var y))).imp
      (FOL.existsAt x φ)) :=
  ⟨exists_alpha_forward φ x y hxy hy, exists_alpha_reverse φ x y hy⟩


def renameSub (x z : Nat) : Nat → Peano.Term := fun a => if a = x then .var z else .var a

def bindName (y : Nat) : Nat → Nat ⊕ Fin 1 := fun a => if a = y then .inr 0 else .inl a

theorem term_bind_rename_comm (x z y n : Nat) (hxy : x ≠ y) (hzy : z ≠ y)
    (t : Peano.language.Term (Nat ⊕ Fin n)) :
    (t.relabel (BoundedFormula.relabelAux (bindName y) n)).subst
      (SyntaxTransport.liftSub (1+n) (renameSub x z)) =
    (t.subst (SyntaxTransport.liftSub n (renameSub x z))).relabel
      (BoundedFormula.relabelAux (bindName y) n) := by
  rw [SyntaxTransport.term_relabel_subst, SyntaxTransport.term_subst_relabel]
  congr 1
  funext a
  cases a with
  | inl a =>
    by_cases ha : a = x
    · subst a
      simp [BoundedFormula.relabelAux, bindName, SyntaxTransport.liftSub, renameSub,
        hxy, hzy, FirstOrder.Language.Term.relabel]
    · by_cases hy : a = y
      · subst a
        simp [BoundedFormula.relabelAux, bindName, SyntaxTransport.liftSub, renameSub,
          Ne.symm hxy, FirstOrder.Language.Term.relabel]
      · simp [BoundedFormula.relabelAux, bindName, SyntaxTransport.liftSub, renameSub,
          ha, hy, FirstOrder.Language.Term.relabel]
  | inr a =>
    simp [BoundedFormula.relabelAux, SyntaxTransport.liftSub, FirstOrder.Language.Term.relabel]

/-- Named binding commutes with renaming x to z when neither name is bound. -/
theorem bounded_bind_rename_comm {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (x z y : Nat) (hxy : x ≠ y) (hzy : z ≠ y) :
    (φ.relabel (bindName y)).subst (renameSub x z) =
      (φ.subst (renameSub x z)).relabel (bindName y) := by
  induction φ with
  | falsum => rfl
  | equal t u =>
    change BoundedFormula.equal
      ((t.relabel (BoundedFormula.relabelAux (bindName y) _)).subst
        (SyntaxTransport.liftSub _ (renameSub x z)))
      ((u.relabel (BoundedFormula.relabelAux (bindName y) _)).subst
        (SyntaxTransport.liftSub _ (renameSub x z))) =
      BoundedFormula.equal
      ((t.subst (SyntaxTransport.liftSub _ (renameSub x z))).relabel
        (BoundedFormula.relabelAux (bindName y) _))
      ((u.subst (SyntaxTransport.liftSub _ (renameSub x z))).relabel
        (BoundedFormula.relabelAux (bindName y) _))
    rw [term_bind_rename_comm x z y _ hxy hzy t, term_bind_rename_comm x z y _ hxy hzy u]
  | rel rel ts =>
    change BoundedFormula.rel rel (fun i =>
      ((ts i).relabel (BoundedFormula.relabelAux (bindName y) _)).subst
        (SyntaxTransport.liftSub _ (renameSub x z))) =
      BoundedFormula.rel rel (fun i =>
        ((ts i).subst (SyntaxTransport.liftSub _ (renameSub x z))).relabel
        (BoundedFormula.relabelAux (bindName y) _))
    congr 1
    funext i
    exact term_bind_rename_comm x z y _ hxy hzy (ts i)
  | imp a b ia ib =>
    simpa only [BoundedFormula.relabel_imp, BoundedFormula.subst,
      BoundedFormula.mapTermRel] using congrArg₂ BoundedFormula.imp ia ib
  | all f ih =>
    simpa only [BoundedFormula.relabel_all, BoundedFormula.subst,
      BoundedFormula.mapTermRel, id_eq] using congrArg BoundedFormula.all ih

theorem subst_var_allAt (φ : Peano.Formula) (x z y : Nat)
    (hxy : x ≠ y) (hzy : z ≠ y) :
    FOL.substAt (FOL.allAt y φ) x (.var z) =
      FOL.allAt y (FOL.substAt φ x (.var z)) := by
  unfold FOL.substAt FOL.allAt
  change ((BoundedFormula.relabel (bindName y) φ).subst (renameSub x z)).all =
    (BoundedFormula.relabel (bindName y) (φ.subst (renameSub x z))).all
  exact congrArg BoundedFormula.all (bounded_bind_rename_comm φ x z y hxy hzy)

theorem subst_var_existsAt (φ : Peano.Formula) (x z y : Nat)
    (hxy : x ≠ y) (hzy : z ≠ y) :
    FOL.substAt (FOL.existsAt y φ) x (.var z) =
      FOL.existsAt y (FOL.substAt φ x (.var z)) := by
  unfold FOL.existsAt
  unfold FOL.substAt at *
  change (((FOL.allAt y φ.not).subst (renameSub x z)).not) =
    (FOL.allAt y ((φ.subst (renameSub x z)).not)).not
  apply congrArg BoundedFormula.not
  have h := subst_var_allAt φ.not x z y hxy hzy
  unfold FOL.substAt at h
  exact h

private theorem substAt_of_fresh (φ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (hx : x ∉ φ.freeVarFinset) : FOL.substAt φ x t = φ := by
  unfold FOL.substAt
  calc
    φ.subst (fun y => if y = x then t else .var y) = φ.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      have hne : y ≠ x := by intro he; subst y; exact hx hy
      simp [hne]
    _ = φ := SyntaxTransport.formula_subst_var _

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl
private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl
private theorem subst_inf (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not, subst_imp, subst_not]
private theorem substAt_imp (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ.imp ψ) x t = (FOL.substAt φ x t).imp (FOL.substAt ψ x t) := by
  exact subst_imp _ _ _
private theorem substAt_inf (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ ⊓ ψ) x t = (FOL.substAt φ x t) ⊓ (FOL.substAt ψ x t) := by
  exact subst_inf _ _ _
private theorem substAt_not (φ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt φ.not x t = (FOL.substAt φ x t).not := by
  exact subst_not _ _
private theorem divides_subst (k d : Peano.Term) (σ : Nat → Peano.Term) :
    (divides k d).subst σ = divides (k.subst σ) (d.subst σ) := by
  unfold divides
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1]

/-- Renaming output code 11 to current code 9 commutes with the exact
three-clause matrix, provided the target relation excludes 11. -/
theorem subst_code_matrix (φ : Peano.Formula) (hφ : 11 ∉ φ.freeVarFinset) :
    FOL.substAt (matrixAt φ (succ (.var 7)) 11 12) 11 (.var 9) =
      matrixAt φ (succ (.var 7)) 9 12 := by
  simp only [matrixAt, rowsAt, factorsAt, futureAt, substAt_inf]
  simp only [subst_var_allAt _ 11 9 2 (by decide) (by decide), substAt_imp,
    subst_var_existsAt _ 11 9 3 (by decide) (by decide), substAt_inf,
    subst_var_existsAt _ 11 9 4 (by decide) (by decide), substAt_not,
    substAt_of_fresh φ 11 (.var 9) hφ]
  simp [FOL.substAt, beta_subst, less_subst, divides_subst,
    FOL.equality_subst, add_subst, mul_subst, succ_subst, PeanoArithmetic.zero_subst,
    CompactArithmetic.modulus, FirstOrder.Language.Term.subst]

/-- Renaming output product 12 to current product 10 commutes with the exact
matrix, provided the target relation excludes 12. -/
theorem subst_product_matrix (φ : Peano.Formula) (hφ : 12 ∉ φ.freeVarFinset) :
    FOL.substAt (matrixAt φ (succ (.var 7)) 9 12) 12 (.var 10) =
      matrixAt φ (succ (.var 7)) 9 10 := by
  simp only [matrixAt, rowsAt, factorsAt, futureAt, substAt_inf]
  simp only [subst_var_allAt _ 12 10 2 (by decide) (by decide), substAt_imp,
    subst_var_existsAt _ 12 10 3 (by decide) (by decide), substAt_inf,
    subst_var_existsAt _ 12 10 4 (by decide) (by decide), substAt_not,
    substAt_of_fresh φ 12 (.var 10) hφ]
  simp [FOL.substAt, beta_subst, less_subst, divides_subst,
    FOL.equality_subst, add_subst, mul_subst, succ_subst, PeanoArithmetic.zero_subst,
    CompactArithmetic.modulus, FirstOrder.Language.Term.subst]

/-- Product renaming under the already-renamed code existential. -/
theorem subst_product_under_code (φ : Peano.Formula) (hφ : 12 ∉ φ.freeVarFinset) :
    FOL.substAt (FOL.existsAt 9 (matrixAt φ (succ (.var 7)) 9 12)) 12 (.var 10) =
      FOL.existsAt 9 (matrixAt φ (succ (.var 7)) 9 10) := by
  rw [subst_var_existsAt _ 12 10 9 (by decide) (by decide), subst_product_matrix φ hφ]


/-- A PA implication lifts through an existential binder. -/
theorem exists_map (φ ψ : Peano.Formula) (x : Nat) (h : FormulaProves (φ.imp ψ)) :
    FormulaProves ((FOL.existsAt x φ).imp (FOL.existsAt x ψ)) := by
  have hi : FormulaProves (ψ.imp (FOL.existsAt x ψ)) := by
    simpa only [SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) ψ x (.var x))
  have hf : x ∉ (FOL.existsAt x ψ).freeVarFinset := by
    simp [FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]
  exact PeanoBitPositionReduction.exists_elim x hf (FOL.Derivation.compose h hi)

private theorem fv_inf (φ ψ : Peano.Formula) :
    (φ ⊓ ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  change ((φ.imp ψ.not).not).freeVarFinset = _
  simp [FirstOrder.Language.BoundedFormula.freeVarFinset]

private theorem fv_exists (φ : Peano.Formula) (x : Nat) :
    (FOL.existsAt x φ).freeVarFinset = φ.freeVarFinset.erase x := by
  simp [FOL.existsAt, SyntaxTransport.allAt_freeVars,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]

/-- The old code-name is fresh before renaming. -/
theorem matrix_fresh9 (φ : Peano.Formula) (hφ9 : 9 ∉ φ.freeVarFinset) :
    9 ∉ (matrixAt φ (succ (.var 7)) 11 12).freeVarFinset := by
  have ha : 9 ∉ (less (.var 2) (succ (.var 7))).freeVarFinset := by decide
  have hb : 9 ∉ (beta (.var 11) (.var 1) (.var 2) (.var 3)).freeVarFinset := by decide
  have hc : 9 ∉ (PeanoDivisibility.divides (modulus (.var 1) (.var 2)) (.var 12)).freeVarFinset := by decide
  have hd : 9 ∉ (less (.var 2) (.var 8)).freeVarFinset := by decide
  have he : 9 ∉ (((mul (.var 12) (.var 3)).equal
    (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2)))) : Peano.Formula)).freeVarFinset := by decide
  simp [matrixAt, rowsAt, factorsAt, futureAt, fv_exists, fv_inf,
    SyntaxTransport.allAt_freeVars, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.freeVarFinset, hφ9, ha, hb, hc, hd, he]

/-- The old product-name is fresh before its rename. -/
theorem matrix_fresh10 (φ : Peano.Formula) (hφ10 : 10 ∉ φ.freeVarFinset) :
    10 ∉ (FOL.existsAt 9 (matrixAt φ (succ (.var 7)) 9 12)).freeVarFinset := by
  have ha : 10 ∉ (less (.var 2) (succ (.var 7))).freeVarFinset := by decide
  have hb : 10 ∉ (beta (.var 9) (.var 1) (.var 2) (.var 3)).freeVarFinset := by decide
  have hc : 10 ∉ (PeanoDivisibility.divides (modulus (.var 1) (.var 2)) (.var 12)).freeVarFinset := by decide
  have hd : 10 ∉ (less (.var 2) (.var 8)).freeVarFinset := by decide
  have he : 10 ∉ (((mul (.var 12) (.var 3)).equal
    (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2)))) : Peano.Formula)).freeVarFinset := by decide
  simp [matrixAt, rowsAt, factorsAt, futureAt, fv_exists, fv_inf,
    SyntaxTransport.allAt_freeVars, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.freeVarFinset, hφ10, ha, hb, hc, hd, he]

/-- Two checked matrix-renaming equalities and stated fresh names imply the
PA proof transport from the 11/12 to the 9/10 CRT witness naming. -/
theorem conditional_alpha (φ : Peano.Formula)
    (h9 : 9 ∉ (matrixAt φ (succ (.var 7)) 11 12).freeVarFinset)
    (h10 : 10 ∉ (FOL.existsAt 9 (matrixAt φ (succ (.var 7)) 9 12)).freeVarFinset)
    (hrow : FOL.substAt (matrixAt φ (succ (.var 7)) 11 12) 11 (.var 9) =
      matrixAt φ (succ (.var 7)) 9 12)
    (hprod : FOL.substAt (FOL.existsAt 9 (matrixAt φ (succ (.var 7)) 9 12)) 12 (.var 10) =
      FOL.existsAt 9 (matrixAt φ (succ (.var 7)) 9 10)) :
    FormulaProves ((nextInvariant φ).imp (invariantAt φ (succ (.var 7)))) := by
  let M := matrixAt φ (succ (.var 7)) 11 12
  let Q := matrixAt φ (succ (.var 7)) 9 12
  have ha := (exists_alpha M 11 9 (by decide) h9).1
  have ha' : FormulaProves ((FOL.existsAt 11 M).imp (FOL.existsAt 9 Q)) := by
    simpa only [M,Q,hrow] using ha
  have hb := exists_map _ _ 12 ha'
  have hc := (exists_alpha (FOL.existsAt 9 Q) 12 10 (by decide) h10).1
  have hc' : FormulaProves ((FOL.existsAt 12 (FOL.existsAt 9 Q)).imp
      (FOL.existsAt 10 (FOL.existsAt 9 (matrixAt φ (succ (.var 7)) 9 10)))) := by
    simpa only [Q,hprod] using hc
  exact FOL.Derivation.compose hb hc'
/-- The matrix substitution equalities alone remain to be discharged under
explicit freshness of the relation formula. -/
theorem conditional_alpha_fresh (φ : Peano.Formula)
    (h9 : 9 ∉ φ.freeVarFinset) (h10 : 10 ∉ φ.freeVarFinset)
    (hrow : FOL.substAt (matrixAt φ (succ (.var 7)) 11 12) 11 (.var 9) =
      matrixAt φ (succ (.var 7)) 9 12)
    (hprod : FOL.substAt (FOL.existsAt 9 (matrixAt φ (succ (.var 7)) 9 12)) 12 (.var 10) =
      FOL.existsAt 9 (matrixAt φ (succ (.var 7)) 9 10)) :
    FormulaProves ((nextInvariant φ).imp (invariantAt φ (succ (.var 7)))) :=
  conditional_alpha φ (matrix_fresh9 φ h9) (matrix_fresh10 φ h10) hrow hprod


/-- The fresh output witness names 11 and 12 may be replaced by the original
names 9 and 10 using an actual PA derivation. The target relation must be
fresh in all four names, preventing capture of its parameters. -/
theorem alpha_next (φ : Peano.Formula)
    (h9 : 9 ∉ φ.freeVarFinset) (h10 : 10 ∉ φ.freeVarFinset)
    (h11 : 11 ∉ φ.freeVarFinset) (h12 : 12 ∉ φ.freeVarFinset) :
    FormulaProves ((nextInvariant φ).imp (invariantAt φ (succ (.var 7)))) :=
  conditional_alpha_fresh φ h9 h10 (subst_code_matrix φ h11)
    (subst_product_under_code φ h12)

end PASoundness.PeanoBetaCRTAlpha
