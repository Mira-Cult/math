import PASoundness.PeanoFiniteComprehensionBase
import PASoundness.PeanoBetaCRTDependentLift

/-! Conditional packaging of the two selector-successor branches.
The selected and unselected branch derivations remain explicit premises.
This file does not prove the successor branches or finite comprehension. -/
namespace PASoundness.PeanoFiniteComprehensionStepPackage
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoFiniteComprehensionBase

def selected (φ : Peano.Formula) : Peano.Formula :=
  FOL.substAt φ 1 (.var 0)

def newPower : Peano.Term := add (.var 2) (.var 2)
def chosenCode : Peano.Term := add (.var 2) (.var 3)

/-- The exposed successor matrix with a specified code and the doubled old power. -/
def updatedMatrix (φ : Peano.Formula) (code : Peano.Term) : Peano.Formula :=
  pow2 (succ (.var 0)) newPower ⊓
    (less code newPower ⊓ rows φ (succ (.var 0)) code)

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

private theorem power_matrix (φ : Peano.Formula) (hφ2 : 2 ∉ φ.freeVarFinset) :
    FOL.substAt (matrix φ (succ (.var 0))) 2 newPower =
      updatedMatrix φ (.var 3) := by
  have hsub := PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh φ 2 newPower hφ2
  unfold matrix updatedMatrix rows
  rw [subst_and, subst_and, subst_all _ 2 1 newPower (by decide) (by decide),
    subst_imp, subst_and, subst_imp, subst_imp, hsub]
  simp [FOL.substAt, newPower, pow2_subst, less_subst, bitFormula_subst, succ_subst,
    FirstOrder.Language.Term.subst]

private theorem code_matrix (φ : Peano.Formula) (hφ3 : 3 ∉ φ.freeVarFinset)
    (code : Peano.Term) (hcode : 1 ∉ code.varFinset) :
    FOL.substAt (updatedMatrix φ (.var 3)) 3 code = updatedMatrix φ code := by
  have hsub := PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh φ 3 code hφ3
  unfold updatedMatrix rows
  rw [subst_and, subst_and, subst_all _ 3 1 code (by decide) hcode,
    subst_imp, subst_and, subst_imp, subst_imp, hsub]
  simp [FOL.substAt, newPower, pow2_subst, less_subst, bitFormula_subst, succ_subst,
    FirstOrder.Language.Term.subst]

/-- PA can package either chosen successor code while preserving the original
relation. The chosen code may use the old p=2 and a=3; it must avoid index 1. -/
theorem package_matrix (φ : Peano.Formula)
    (hφ2 : 2 ∉ φ.freeVarFinset) (hφ3 : 3 ∉ φ.freeVarFinset)
    (code : Peano.Term) (hcode : 1 ∉ code.varFinset) :
    FormulaProves ((updatedMatrix φ code).imp (invariant φ (succ (.var 0)))) := by
  let M := matrix φ (succ (.var 0))
  let P := updatedMatrix φ (.var 3)
  have he3 : FormulaProves ((updatedMatrix φ code).imp (FOL.existsAt 3 P)) := by
    have h := FOL.Derivation.existsIntro (A := Peano.Axiom) P 3 code
    rw [show FOL.substAt P 3 code = updatedMatrix φ code from code_matrix φ hφ3 code hcode] at h
    exact h
  have he2 := FOL.Derivation.existsIntro (A := Peano.Axiom) (FOL.existsAt 3 M) 2 newPower
  have hs : FOL.substAt (FOL.existsAt 3 M) 2 newPower = FOL.existsAt 3 P := by
    rw [subst_exists M 2 3 newPower (by decide) (by decide), power_matrix φ hφ2]
  rw [hs] at he2
  exact FOL.Derivation.compose he3 (by simpa only [invariant, M] using he2)

private theorem split_state (M S T : Peano.Formula)
    (hf2 : 2 ∉ T.freeVarFinset) (hf3 : 3 ∉ T.freeVarFinset)
    (htrue : FormulaProves (M.imp (S.imp T)))
    (hfalse : FormulaProves (M.imp (S.not.imp T))) :
    FormulaProves ((FOL.existsAt 2 (FOL.existsAt 3 M)).imp T) := by
  have hbody : FormulaProves (M.imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.dne
    apply FOL.Context.deduction
    let Γ := [T.not,M]
    have hm : FOL.Context Peano.Axiom Γ M := .hypothesis (by simp [Γ])
    have hn : FOL.Context Peano.Axiom Γ T.not := FOL.Context.head _ _
    have ht : FOL.Context Peano.Axiom Γ (S.imp T) := .mp (.closed htrue) hm
    have hf : FOL.Context Peano.Axiom Γ (S.not.imp T) := .mp (.closed hfalse) hm
    have hns : FOL.Context Peano.Axiom Γ S.not := .mp (FOL.Context.contrapose ht) hn
    exact .mp hn (.mp hf hns)
  have h3 := PeanoBitPositionReduction.exists_elim 3 hf3 hbody
  exact PeanoBitPositionReduction.exists_elim 2 hf2 h3

/-- Conditional PA successor: both literal branch matrices are explicit
derivation premises. This does not assert either branch. -/
theorem successor_of_branches (φ : Peano.Formula)
    (hφ2 : 2 ∉ φ.freeVarFinset) (hφ3 : 3 ∉ φ.freeVarFinset)
    (htrue : FormulaProves ((matrix φ (.var 0)).imp
      ((selected φ).imp (updatedMatrix φ chosenCode))))
    (hfalse : FormulaProves ((matrix φ (.var 0)).imp
      ((selected φ).not.imp (updatedMatrix φ (.var 3))))) :
    FormulaProves ((invariant φ (.var 0)).imp (invariant φ (succ (.var 0)))) := by
  let M := matrix φ (.var 0)
  let S := selected φ
  let T := invariant φ (succ (.var 0))
  have ht : FormulaProves (M.imp (S.imp T)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hm : FOL.Context Peano.Axiom [S,M] M := .hypothesis (by simp)
    have hs : FOL.Context Peano.Axiom [S,M] S := FOL.Context.head _ _
    exact .mp (.closed (package_matrix φ hφ2 hφ3 chosenCode (by decide)))
      (.mp (.mp (.closed htrue) hm) hs)
  have hf : FormulaProves (M.imp (S.not.imp T)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hm : FOL.Context Peano.Axiom [S.not,M] M := .hypothesis (by simp)
    have hs : FOL.Context Peano.Axiom [S.not,M] S.not := FOL.Context.head _ _
    exact .mp (.closed (package_matrix φ hφ2 hφ3 (.var 3) (by decide)))
      (.mp (.mp (.closed hfalse) hm) hs)
  have hf2 : 2 ∉ T.freeVarFinset := by
    simp [T, invariant, FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]
  have hf3 : 3 ∉ T.freeVarFinset := by
    simp [T, invariant, FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]
  exact split_state M S T hf2 hf3 ht hf

end PASoundness.PeanoFiniteComprehensionStepPackage

#print axioms PASoundness.PeanoFiniteComprehensionStepPackage.package_matrix
#print axioms PASoundness.PeanoFiniteComprehensionStepPackage.successor_of_branches
