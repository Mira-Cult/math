import PASoundness.PeanoPowerExistenceBase
import PASoundness.PeanoBetaCRTAlignment
import PASoundness.PeanoBetaCRTPrefixSubst

/-! The empty-prefix case of a bounded finite-comprehension invariant.
This file does not assert its successor step or finite comprehension. -/
namespace PASoundness.PeanoFiniteComprehensionBase
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- At each index below k, the literal bit agrees with the supplied formula.
Name 1 is the index; φ may use arbitrary other parameters. -/
def rows (φ : Peano.Formula) (k a : Peano.Term) : Peano.Formula :=
  FOL.allAt 1 ((less (.var 1) k).imp
    (((bitFormula a (.var 1)).imp φ) ⊓ (φ.imp (bitFormula a (.var 1)))))

/-- Power and code are names 2 and 3. -/
def matrix (φ : Peano.Formula) (k : Peano.Term) : Peano.Formula :=
  (pow2 k (.var 2)) ⊓ ((less (.var 3) (.var 2)) ⊓ (rows φ k (.var 3)))

def invariant (φ : Peano.Formula) (k : Peano.Term) : Peano.Formula :=
  FOL.existsAt 2 (FOL.existsAt 3 (matrix φ k))

/-- Every empty prefix agrees with every relation, regardless of its values. -/
theorem empty_rows (φ : Peano.Formula) (a : Peano.Term) :
    FormulaProves (rows φ zero a) := by
  unfold rows
  apply FOL.Derivation.generalize
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  exact FOL.Context.explode _
    (.mp (.closed (PeanoEmptyBitSet.no_less_zero (.var 1))) (FOL.Context.head [] _))

private theorem subst_all (φ : Peano.Formula) (x y : Nat) (t : Peano.Term)
    (hxy : y ≠ x) (ht : y ∉ t.varFinset) :
    FOL.substAt (FOL.allAt y φ) x t = FOL.allAt y (FOL.substAt φ x t) := by
  unfold FOL.substAt
  apply PeanoBetaCRTAlignment.arbitrary_subst_all_at _ y
  · simp [hxy]
  · intro z hz
    by_cases h : z = x
    · simp [h, ht]
    · simp [h, Ne.symm hz]

private theorem subst_exists (φ : Peano.Formula) (x y : Nat) (t : Peano.Term)
    (hxy : y ≠ x) (ht : y ∉ t.varFinset) :
    FOL.substAt (FOL.existsAt y φ) x t = FOL.existsAt y (FOL.substAt φ x t) := by
  unfold FOL.substAt
  apply PeanoBetaCRTAlignment.arbitrary_subst_exists_at _ y
  · simp [hxy]
  · intro z hz
    by_cases h : z = x
    · simp [h, ht]
    · simp [h, Ne.symm hz]

private theorem subst_and (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ ⊓ ψ) x t = (FOL.substAt φ x t) ⊓ (FOL.substAt ψ x t) := rfl

private theorem subst_imp (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ.imp ψ) x t = (FOL.substAt φ x t).imp (FOL.substAt ψ x t) := rfl

private theorem rows_subst_code (φ : Peano.Formula) (hφ : 3 ∉ φ.freeVarFinset) :
    FOL.substAt (rows φ zero (.var 3)) 3 zero = rows φ zero zero := by
  unfold rows
  rw [subst_all _ 3 1 zero (by decide) (by decide), subst_imp, subst_and, subst_imp, subst_imp]
  have hsub : φ.subst (fun y => if y = 3 then zero else .var y) = φ := by
    exact PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh φ 3 zero hφ
  simp [FOL.substAt, less_subst, bitFormula_subst, PeanoArithmetic.zero_subst,
    FirstOrder.Language.Term.subst, hsub]

private theorem rows_subst_power (φ : Peano.Formula) (hφ : 2 ∉ φ.freeVarFinset) :
    FOL.substAt (rows φ zero (.var 3)) 2 (succ zero) = rows φ zero (.var 3) := by
  unfold rows
  rw [subst_all _ 2 1 (succ zero) (by decide) (by decide), subst_imp, subst_and, subst_imp, subst_imp]
  have hsub : φ.subst (fun y => if y = 2 then succ zero else .var y) = φ := by
    exact PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh φ 2 (succ zero) hφ
  simp [FOL.substAt, less_subst, bitFormula_subst, PeanoArithmetic.zero_subst,
    FirstOrder.Language.Term.subst, hsub]

private def matrixOne (φ : Peano.Formula) : Peano.Formula :=
  (pow2 zero (succ zero)) ⊓ ((less (.var 3) (succ zero)) ⊓ (rows φ zero (.var 3)))

private theorem matrix_subst_power (φ : Peano.Formula) (hφ : 2 ∉ φ.freeVarFinset) :
    FOL.substAt (matrix φ zero) 2 (succ zero) = matrixOne φ := by
  unfold matrix matrixOne
  rw [subst_and, subst_and, rows_subst_power φ hφ]
  simp [FOL.substAt, pow2_subst, less_subst, PeanoArithmetic.zero_subst,
    FirstOrder.Language.Term.subst]

private theorem matrixOne_subst_code (φ : Peano.Formula) (hφ : 3 ∉ φ.freeVarFinset) :
    FOL.substAt (matrixOne φ) 3 zero =
      (pow2 zero (succ zero)) ⊓ ((less zero (succ zero)) ⊓ (rows φ zero zero)) := by
  unfold matrixOne
  rw [subst_and, subst_and, rows_subst_code φ hφ]
  simp [FOL.substAt, pow2_subst, less_subst, PeanoArithmetic.zero_subst,
    PeanoArithmetic.succ_subst, FirstOrder.Language.Term.subst]

/-- With p=1 and a=0, PA proves the base invariant. Freshness ensures φ
denotes the same relation under the two witness introductions. -/
theorem base (φ : Peano.Formula) (hφ2 : 2 ∉ φ.freeVarFinset)
    (hφ3 : 3 ∉ φ.freeVarFinset) : FormulaProves (invariant φ zero) := by
  let M := matrixOne φ
  have hm : FormulaProves (FOL.substAt M 3 zero) := by
    rw [matrixOne_subst_code φ hφ3]
    apply FOL.Context.closeEmpty
    exact FOL.Context.conjunctionIntro (.closed PeanoPowerExistenceBase.pow2_zero_one)
      (FOL.Context.conjunctionIntro (.closed (PeanoOrderTotality.zero_less_succ zero))
        (.closed (empty_rows φ zero)))
  have he3 : FormulaProves (FOL.existsAt 3 M) :=
    .mp (FOL.Derivation.existsIntro M 3 zero) hm
  have hi2 := FOL.Derivation.existsIntro (A := Peano.Axiom)
    (FOL.existsAt 3 (matrix φ zero)) 2 (succ zero)
  have hs : FOL.substAt (FOL.existsAt 3 (matrix φ zero)) 2 (succ zero) =
      FOL.existsAt 3 M := by
    rw [subst_exists _ 2 3 (succ zero) (by decide) (by decide), matrix_subst_power φ hφ2]
  rw [hs] at hi2
  exact .mp hi2 he3

end PASoundness.PeanoFiniteComprehensionBase

#print axioms PASoundness.PeanoFiniteComprehensionBase.empty_rows
#print axioms PASoundness.PeanoFiniteComprehensionBase.base
