import PASoundness.PeanoBetaCRTProjection
import PASoundness.PeanoBetaAppendCRT

/-! PA existence of a single beta code for the append relation. This does
not yet construct a power trace or assert power totality. -/
namespace PASoundness.PeanoBetaAppendRowsExist
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaCRTInvariant PeanoBetaCRTProjection PeanoBetaAppendCRT
open PeanoBetaAppendRelation PeanoBetaCRTParameter

/-- The new parameter and the new code witness all requested append rows. -/
def appendedRows : Peano.Formula :=
  FOL.existsAt 1 (FOL.existsAt 9 (rowsAt appendRelation endIndex 9))

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

private theorem relation_fresh : 8 ∉ appendRelation.freeVarFinset := by decide
private theorem beta_fresh : 8 ∉ (beta (.var 9) (.var 1) (.var 2) (.var 3)).freeVarFinset := by decide
private theorem coded_fresh : 16 ∉ (codedRows appendRelation).freeVarFinset := by decide

private theorem rows_sub : FOL.substAt (rowsAt appendRelation (.var 8) 9) 8 endIndex =
    rowsAt appendRelation endIndex 9 := by
  unfold rowsAt
  rw [sa _ 8 2 _ (by decide) (by decide)]
  congr 1
  change ((FOL.substAt (less (.var 2) (.var 8)) 8 endIndex).imp
    (FOL.substAt (FOL.existsAt 3 (appendRelation ⊓
      beta (.var 9) (.var 1) (.var 2) (.var 3))) 8 endIndex)) = _
  rw [se _ 8 3 _ (by decide) (by decide)]
  change ((FOL.substAt (less (.var 2) (.var 8)) 8 endIndex).imp
    (FOL.existsAt 3 ((FOL.substAt appendRelation 8 endIndex) ⊓
      (FOL.substAt (beta (.var 9) (.var 1) (.var 2) (.var 3)) 8 endIndex)))) = _
  rw [PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh _ _ _ relation_fresh,
    PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh _ _ _ beta_fresh]
  simp [FOL.substAt, less_subst, FirstOrder.Language.Term.subst]

/-- Substitution of both CRT parameters changes the bound but leaves the
append relation and its code/parameter witnesses intact. -/
theorem projected_syntax : (codedRows appendRelation).subst σ = appendedRows := by
  rw [← specialization_syntax,
    PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh _ _ _ coded_fresh]
  unfold codedRows appendedRows
  rw [se _ 8 1 _ (by decide) (by decide), se _ 8 9 _ (by decide) (by decide), rows_sub]

/-- PA constructs a single parameter and code for all append rows. The
displayed old code, old parameter, length and appended value are free. -/
theorem append_rows_exist : FormulaProves appendedRows := by
  let F := (boundedSolvedParameter appendRelation).imp (codedRows appendRelation)
  have hfresh : 10 ∉ appendRelation.freeVarFinset := by decide
  have h : FormulaProves F := bounded_solution_to_coded_rows appendRelation hfresh
  have h16 : FormulaProves (FOL.substAt F 16 traceBound) := .mp
    (.logical (.allElim F 16 traceBound)) (.generalize 16 h)
  have h8 : FormulaProves (FOL.substAt (FOL.substAt F 16 traceBound) 8 endIndex) := .mp
    (.logical (.allElim (FOL.substAt F 16 traceBound) 8 endIndex)) (.generalize 8 h16)
  rw [specialization_syntax] at h8
  change FormulaProves (((boundedSolvedParameter appendRelation).subst σ).imp
    ((codedRows appendRelation).subst σ)) at h8
  rw [projected_syntax] at h8
  have hs : FormulaProves ((boundedSolvedParameter appendRelation).subst σ) := by
    change FormulaProves appendSolved
    rw [solved_syntax]
    exact append_crt_exists
  exact .mp h8 hs

end PASoundness.PeanoBetaAppendRowsExist

#print axioms PASoundness.PeanoBetaAppendRowsExist.append_rows_exist
