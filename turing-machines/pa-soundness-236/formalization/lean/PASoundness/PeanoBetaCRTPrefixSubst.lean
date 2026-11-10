import PASoundness.PeanoBetaCRTInvariant

/-! Capture-safe zero and successor substitution through the fixed-name CRT
invariant. These are syntax equalities, not CRT update or induction proofs. -/

namespace PASoundness.PeanoBetaCRTPrefixSubst.Syntax
open FirstOrder FirstOrder.Language
open Peano

/-- Substituting any term for a name absent from a PA formula leaves it
unchanged. This uses syntax alone, and applies to arbitrary user formula φ. -/
theorem substAt_of_fresh (φ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (hx : x ∉ φ.freeVarFinset) : FOL.substAt φ x t = φ := by
  unfold FOL.substAt
  calc
    φ.subst (fun y => if y = x then t else .var y) = φ.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      have hne : y ≠ x := by
        intro he
        subst y
        exact hx hy
      simp [hne]
    _ = φ := SyntaxTransport.formula_subst_var _


def zeroSub (x : Nat) : Nat → Peano.Term := fun z => if z = x then Peano.zero else .var z

def bindName (y : Nat) : Nat → Nat ⊕ Fin 1 := fun z => if z = y then .inr 0 else .inl z

theorem term_bind_zero_comm (x y n : Nat) (hxy : x ≠ y)
    (t : Peano.language.Term (Nat ⊕ Fin n)) :
    (t.relabel (BoundedFormula.relabelAux (bindName y) n)).subst
      (SyntaxTransport.liftSub (1+n) (zeroSub x)) =
    (t.subst (SyntaxTransport.liftSub n (zeroSub x))).relabel
      (BoundedFormula.relabelAux (bindName y) n) := by
  rw [SyntaxTransport.term_relabel_subst, SyntaxTransport.term_subst_relabel]
  congr 1
  funext z
  cases z with
  | inl z =>
    by_cases hz : z = x
    · subst z
      simp [BoundedFormula.relabelAux, bindName, SyntaxTransport.liftSub, zeroSub,
        hxy, Peano.zero, FirstOrder.Language.Term.relabel]
      congr 1
      funext i
      exact Fin.elim0 i
    · by_cases hy : z = y
      · subst z
        simp [BoundedFormula.relabelAux, bindName, SyntaxTransport.liftSub, zeroSub,
          Ne.symm hxy, FirstOrder.Language.Term.relabel]
      · simp [BoundedFormula.relabelAux, bindName, SyntaxTransport.liftSub, zeroSub,
          hz, hy, FirstOrder.Language.Term.relabel]
  | inr z =>
    simp [BoundedFormula.relabelAux, SyntaxTransport.liftSub, FirstOrder.Language.Term.relabel]


theorem bounded_bind_zero_comm {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (x y : Nat) (hxy : x ≠ y) :
    (φ.relabel (bindName y)).subst (zeroSub x) =
      (φ.subst (zeroSub x)).relabel (bindName y) := by
  induction φ with
  | falsum => rfl
  | equal t u =>
    change BoundedFormula.equal
      ((t.relabel (BoundedFormula.relabelAux (bindName y) _)).subst
        (SyntaxTransport.liftSub _ (zeroSub x)))
      ((u.relabel (BoundedFormula.relabelAux (bindName y) _)).subst
        (SyntaxTransport.liftSub _ (zeroSub x))) =
      BoundedFormula.equal
      ((t.subst (SyntaxTransport.liftSub _ (zeroSub x))).relabel
        (BoundedFormula.relabelAux (bindName y) _))
      ((u.subst (SyntaxTransport.liftSub _ (zeroSub x))).relabel
        (BoundedFormula.relabelAux (bindName y) _))
    rw [term_bind_zero_comm x y _ hxy t, term_bind_zero_comm x y _ hxy u]
  | rel rel ts =>
    change BoundedFormula.rel rel (fun i =>
      ((ts i).relabel (BoundedFormula.relabelAux (bindName y) _)).subst
        (SyntaxTransport.liftSub _ (zeroSub x))) =
      BoundedFormula.rel rel (fun i =>
        ((ts i).subst (SyntaxTransport.liftSub _ (zeroSub x))).relabel
          (BoundedFormula.relabelAux (bindName y) _))
    congr 1
    funext i
    exact term_bind_zero_comm x y _ hxy (ts i)
  | imp a b ia ib =>
    simpa only [BoundedFormula.relabel_imp, BoundedFormula.subst,
      BoundedFormula.mapTermRel] using congrArg₂ BoundedFormula.imp ia ib
  | all f ih =>
    simpa only [BoundedFormula.relabel_all, BoundedFormula.subst,
      BoundedFormula.mapTermRel, id_eq] using congrArg BoundedFormula.all ih


/-- Substitution of the closed term zero for x commutes with binding a
separate name y in any PA formula. -/
theorem subst_zero_allAt (φ : Peano.Formula) (x y : Nat) (hxy : x ≠ y) :
    FOL.substAt (FOL.allAt y φ) x Peano.zero =
      FOL.allAt y (FOL.substAt φ x Peano.zero) := by
  unfold FOL.substAt FOL.allAt
  change ((BoundedFormula.relabel (bindName y) φ).subst (zeroSub x)).all =
    (BoundedFormula.relabel (bindName y) (φ.subst (zeroSub x))).all
  exact congrArg BoundedFormula.all (bounded_bind_zero_comm φ x y hxy)

/-- Existential form of the same binder/substitution law. -/
theorem subst_zero_existsAt (φ : Peano.Formula) (x y : Nat) (hxy : x ≠ y) :
    FOL.substAt (FOL.existsAt y φ) x Peano.zero =
      FOL.existsAt y (FOL.substAt φ x Peano.zero) := by
  unfold FOL.existsAt
  unfold FOL.substAt at *
  change (((FOL.allAt y φ.not).subst (zeroSub x)).not) =
    (FOL.allAt y ((φ.subst (zeroSub x)).not)).not
  apply congrArg BoundedFormula.not
  have h := subst_zero_allAt φ.not x y hxy
  unfold FOL.substAt at h
  exact h


def succSelfSub (x : Nat) : Nat → Peano.Term := fun z => if z = x then Peano.succ (.var x) else .var z

theorem term_bind_succSelf_comm (x y n : Nat) (hxy : x ≠ y)
    (t : Peano.language.Term (Nat ⊕ Fin n)) :
    (t.relabel (BoundedFormula.relabelAux (bindName y) n)).subst
      (SyntaxTransport.liftSub (1+n) (succSelfSub x)) =
    (t.subst (SyntaxTransport.liftSub n (succSelfSub x))).relabel
      (BoundedFormula.relabelAux (bindName y) n) := by
  rw [SyntaxTransport.term_relabel_subst, SyntaxTransport.term_subst_relabel]
  congr 1
  funext z
  cases z with
  | inl z =>
    by_cases hz : z = x
    · subst z
      simp [BoundedFormula.relabelAux, bindName, SyntaxTransport.liftSub, succSelfSub,
        hxy, Peano.succ, FirstOrder.Language.Term.relabel]
    · by_cases hy : z = y
      · subst z
        simp [BoundedFormula.relabelAux, bindName, SyntaxTransport.liftSub, succSelfSub,
          Ne.symm hxy, FirstOrder.Language.Term.relabel]
      · simp [BoundedFormula.relabelAux, bindName, SyntaxTransport.liftSub, succSelfSub,
          hz, hy, FirstOrder.Language.Term.relabel]
  | inr z =>
    simp [BoundedFormula.relabelAux, SyntaxTransport.liftSub, FirstOrder.Language.Term.relabel]


theorem bounded_bind_succSelf_comm {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (x y : Nat) (hxy : x ≠ y) :
    (φ.relabel (bindName y)).subst (succSelfSub x) =
      (φ.subst (succSelfSub x)).relabel (bindName y) := by
  induction φ with
  | falsum => rfl
  | equal t u =>
    change BoundedFormula.equal
      ((t.relabel (BoundedFormula.relabelAux (bindName y) _)).subst
        (SyntaxTransport.liftSub _ (succSelfSub x)))
      ((u.relabel (BoundedFormula.relabelAux (bindName y) _)).subst
        (SyntaxTransport.liftSub _ (succSelfSub x))) =
      BoundedFormula.equal
      ((t.subst (SyntaxTransport.liftSub _ (succSelfSub x))).relabel
        (BoundedFormula.relabelAux (bindName y) _))
      ((u.subst (SyntaxTransport.liftSub _ (succSelfSub x))).relabel
        (BoundedFormula.relabelAux (bindName y) _))
    rw [term_bind_succSelf_comm x y _ hxy t, term_bind_succSelf_comm x y _ hxy u]
  | rel rel ts =>
    change BoundedFormula.rel rel (fun i =>
      ((ts i).relabel (BoundedFormula.relabelAux (bindName y) _)).subst
        (SyntaxTransport.liftSub _ (succSelfSub x))) =
      BoundedFormula.rel rel (fun i =>
        ((ts i).subst (SyntaxTransport.liftSub _ (succSelfSub x))).relabel
          (BoundedFormula.relabelAux (bindName y) _))
    congr 1
    funext i
    exact term_bind_succSelf_comm x y _ hxy (ts i)
  | imp a b ia ib =>
    simpa only [BoundedFormula.relabel_imp, BoundedFormula.subst,
      BoundedFormula.mapTermRel] using congrArg₂ BoundedFormula.imp ia ib
  | all f ih =>
    simpa only [BoundedFormula.relabel_all, BoundedFormula.subst,
      BoundedFormula.mapTermRel, id_eq] using congrArg BoundedFormula.all ih


/-- Substitution of the term successor of x for x commutes with binding a
separate name y in any PA formula. -/
theorem subst_succSelf_allAt (φ : Peano.Formula) (x y : Nat) (hxy : x ≠ y) :
    FOL.substAt (FOL.allAt y φ) x (Peano.succ (.var x)) =
      FOL.allAt y (FOL.substAt φ x (Peano.succ (.var x))) := by
  unfold FOL.substAt FOL.allAt
  change ((BoundedFormula.relabel (bindName y) φ).subst (succSelfSub x)).all =
    (BoundedFormula.relabel (bindName y) (φ.subst (succSelfSub x))).all
  exact congrArg BoundedFormula.all (bounded_bind_succSelf_comm φ x y hxy)

/-- Existential form of self-successor binder law. -/
theorem subst_succSelf_existsAt (φ : Peano.Formula) (x y : Nat) (hxy : x ≠ y) :
    FOL.substAt (FOL.existsAt y φ) x (Peano.succ (.var x)) =
      FOL.existsAt y (FOL.substAt φ x (Peano.succ (.var x))) := by
  unfold FOL.existsAt
  unfold FOL.substAt at *
  change (((FOL.allAt y φ.not).subst (succSelfSub x)).not) =
    (FOL.allAt y ((φ.subst (succSelfSub x)).not)).not
  apply congrArg BoundedFormula.not
  have h := subst_succSelf_allAt φ.not x y hxy
  unfold FOL.substAt at h
  exact h


end PASoundness.PeanoBetaCRTPrefixSubst.Syntax

namespace PASoundness.PeanoBetaCRTPrefixSubst
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoDivisibility
open PeanoBetaCRTInvariant PeanoBetaCRTPrefixSubst.Syntax

private theorem subst_imp (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ.imp ψ) x t = (FOL.substAt φ x t).imp (FOL.substAt ψ x t) := rfl
private theorem subst_not (φ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt φ.not x t = (FOL.substAt φ x t).not := rfl
private theorem subst_and (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ ⊓ ψ) x t = (FOL.substAt φ x t) ⊓ (FOL.substAt ψ x t) := rfl

private theorem lt_sub : FOL.substAt (less (.var 2) (.var 7)) 7 zero = less (.var 2) zero := by
  simp [FOL.substAt, less_subst, FirstOrder.Language.Term.subst]

private theorem lt_fresh : FOL.substAt (less (.var 2) (.var 8)) 7 zero = less (.var 2) (.var 8) := by
  apply substAt_of_fresh
  decide

private theorem row_beta_fresh : FOL.substAt
    (beta (.var 9) (.var 1) (.var 2) (.var 3)) 7 zero =
    beta (.var 9) (.var 1) (.var 2) (.var 3) := by
  apply substAt_of_fresh
  decide

private theorem factor_fresh : FOL.substAt
    (divides (modulus (.var 1) (.var 2)) (.var 10)) 7 zero =
    divides (modulus (.var 1) (.var 2)) (.var 10) := by
  apply substAt_of_fresh
  decide

private theorem inv_fresh : FOL.substAt
    ((mul (.var 10) (.var 3)).equal
      (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2))))) 7 zero =
    ((mul (.var 10) (.var 3)).equal
      (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2))))) := by
  apply substAt_of_fresh
  decide

theorem rows_zero (φ : Peano.Formula) (hφ : 7 ∉ φ.freeVarFinset) :
    FOL.substAt (rowsAt φ (.var 7) 9) 7 zero = rowsAt φ zero 9 := by
  unfold rowsAt
  rw [subst_zero_allAt _ 7 2 (by decide), subst_imp, lt_sub,
    subst_zero_existsAt _ 7 3 (by decide), subst_and,
    substAt_of_fresh φ 7 zero hφ, row_beta_fresh]

theorem factors_zero : FOL.substAt (factorsAt (.var 7) 10) 7 zero = factorsAt zero 10 := by
  unfold factorsAt
  rw [subst_zero_allAt _ 7 2 (by decide), subst_imp, lt_sub, factor_fresh]

theorem future_zero : FOL.substAt (futureAt (.var 7) 10) 7 zero = futureAt zero 10 := by
  unfold futureAt
  rw [subst_zero_allAt _ 7 2 (by decide), subst_imp, subst_and, subst_not, lt_sub, lt_fresh,
    subst_zero_existsAt _ 7 3 (by decide), subst_zero_existsAt _ 7 4 (by decide), inv_fresh]

theorem matrix_zero (φ : Peano.Formula) (hφ : 7 ∉ φ.freeVarFinset) :
    FOL.substAt (matrixAt φ (.var 7) 9 10) 7 zero = matrixAt φ zero 9 10 := by
  unfold matrixAt
  rw [subst_and, subst_and, rows_zero φ hφ, factors_zero, future_zero]

theorem invariant_zero (φ : Peano.Formula) (hφ : 7 ∉ φ.freeVarFinset) :
    FOL.substAt (invariantAt φ (.var 7)) 7 zero = invariantAt φ zero := by
  unfold invariantAt invariantWith
  rw [subst_zero_existsAt _ 7 10 (by decide), subst_zero_existsAt _ 7 9 (by decide), matrix_zero φ hφ]


private theorem lt_succ_sub : FOL.substAt (less (.var 2) (.var 7)) 7 (succ (.var 7)) = less (.var 2) (succ (.var 7)) := by
  simp [FOL.substAt, less_subst, FirstOrder.Language.Term.subst]

private theorem lt_succ_fresh : FOL.substAt (less (.var 2) (.var 8)) 7 (succ (.var 7)) = less (.var 2) (.var 8) := by
  apply substAt_of_fresh
  decide

private theorem row_beta_succ_fresh : FOL.substAt
    (beta (.var 9) (.var 1) (.var 2) (.var 3)) 7 (succ (.var 7)) =
    beta (.var 9) (.var 1) (.var 2) (.var 3) := by
  apply substAt_of_fresh
  decide

private theorem factor_succ_fresh : FOL.substAt
    (divides (modulus (.var 1) (.var 2)) (.var 10)) 7 (succ (.var 7)) =
    divides (modulus (.var 1) (.var 2)) (.var 10) := by
  apply substAt_of_fresh
  decide

private theorem inv_succ_fresh : FOL.substAt
    ((mul (.var 10) (.var 3)).equal
      (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2))))) 7 (succ (.var 7)) =
    ((mul (.var 10) (.var 3)).equal
      (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2))))) := by
  apply substAt_of_fresh
  decide

theorem rows_succ (φ : Peano.Formula) (hφ : 7 ∉ φ.freeVarFinset) :
    FOL.substAt (rowsAt φ (.var 7) 9) 7 (succ (.var 7)) = rowsAt φ (succ (.var 7)) 9 := by
  unfold rowsAt
  rw [subst_succSelf_allAt _ 7 2 (by decide), subst_imp, lt_succ_sub,
    subst_succSelf_existsAt _ 7 3 (by decide), subst_and,
    substAt_of_fresh φ 7 (succ (.var 7)) hφ, row_beta_succ_fresh]

theorem factors_succ : FOL.substAt (factorsAt (.var 7) 10) 7 (succ (.var 7)) = factorsAt (succ (.var 7)) 10 := by
  unfold factorsAt
  rw [subst_succSelf_allAt _ 7 2 (by decide), subst_imp, lt_succ_sub, factor_succ_fresh]

theorem future_succ : FOL.substAt (futureAt (.var 7) 10) 7 (succ (.var 7)) = futureAt (succ (.var 7)) 10 := by
  unfold futureAt
  rw [subst_succSelf_allAt _ 7 2 (by decide), subst_imp, subst_and, subst_not, lt_succ_sub, lt_succ_fresh,
    subst_succSelf_existsAt _ 7 3 (by decide), subst_succSelf_existsAt _ 7 4 (by decide), inv_succ_fresh]

theorem matrix_succ (φ : Peano.Formula) (hφ : 7 ∉ φ.freeVarFinset) :
    FOL.substAt (matrixAt φ (.var 7) 9 10) 7 (succ (.var 7)) = matrixAt φ (succ (.var 7)) 9 10 := by
  unfold matrixAt
  rw [subst_and, subst_and, rows_succ φ hφ, factors_succ, future_succ]

theorem invariant_succ (φ : Peano.Formula) (hφ : 7 ∉ φ.freeVarFinset) :
    FOL.substAt (invariantAt φ (.var 7)) 7 (succ (.var 7)) = invariantAt φ (succ (.var 7)) := by
  unfold invariantAt invariantWith
  rw [subst_succSelf_existsAt _ 7 10 (by decide), subst_succSelf_existsAt _ 7 9 (by decide), matrix_succ φ hφ]


end PASoundness.PeanoBetaCRTPrefixSubst
