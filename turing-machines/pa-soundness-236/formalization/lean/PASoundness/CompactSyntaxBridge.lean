import PASoundness.CompactArithmetic
import PASoundness.SyntaxTransport
import PASoundness.CompactSemantics

/-! Exact syntactic substitution laws for the arithmetic coding formulas. -/
namespace PASoundness.CompactArithmetic
open FirstOrder FirstOrder.Language Peano SyntaxTransport

@[simp] theorem zero_subst (σ : Nat → Peano.Term) : zero.subst σ = zero := by
  unfold zero
  simp only [Term.subst]
  congr 1
  funext i
  exact Fin.elim0 i

theorem less_subst (a b : Peano.Term) (σ : Nat → Peano.Term) :
    (less a b).subst σ = less (a.subst σ) (b.subst σ) := by
  unfold less
  rw [formula_subst_comp]
  congr 1
  funext x
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> simp [h0,h1]

theorem beta_subst (a b c d : Peano.Term) (σ : Nat → Peano.Term) :
    (beta a b c d).subst σ = beta (a.subst σ) (b.subst σ) (c.subst σ) (d.subst σ) := by
  unfold beta
  rw [formula_subst_comp]
  congr 1
  funext x
  match x with
  | 0 | 1 | 2 | 3 => rfl
  | _+4 => exact zero_subst σ

theorem pow2_subst (a b : Peano.Term) (σ : Nat → Peano.Term) :
    (pow2 a b).subst σ = pow2 (a.subst σ) (b.subst σ) := by
  unfold pow2
  rw [formula_subst_comp]
  congr 1
  funext x
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> simp [h0,h1]

theorem bitFormula_subst (a b : Peano.Term) (σ : Nat → Peano.Term) :
    (bitFormula a b).subst σ = bitFormula (a.subst σ) (b.subst σ) := by
  unfold bitFormula
  rw [formula_subst_comp]
  congr 1
  funext x
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> simp [h0,h1]

theorem lessTemplate_freeVars : lessTemplate.freeVarFinset = {0,1} := by decide
theorem betaTemplate_freeVars : betaTemplate.freeVarFinset = {0,1,2,3} := by decide
theorem pow2Template_freeVars : pow2Template.freeVarFinset = {0,1} := by decide
theorem bitTemplate_freeVars : bitTemplate.freeVarFinset = {0,1} := by decide

theorem bitFormula_freeVars (a b : Peano.Term) :
    (bitFormula a b).freeVarFinset = a.varFinset ∪ b.varFinset := by
  ext x
  simp [bitFormula,formula_subst_freeVars,bitTemplate_freeVars]

theorem translate_freeVars (f : CompactMatrix.Formula) :
    (translate f).freeVarFinset = f.freeVars := by
  induction f with
  | truth => simp [translate,CompactMatrix.Formula.freeVars]
  | imp a b ia ib => simp [translate,CompactMatrix.Formula.freeVars,ia,ib]
  | member a b => simp [translate,CompactMatrix.Formula.freeVars,bitFormula_freeVars,v]
  | equal a b => simp [translate,CompactMatrix.Formula.freeVars,Term.equal,Term.bdEqual,v]
  | all x f ih => simp [translate,CompactMatrix.Formula.freeVars,allAt_freeVars,ih]

end PASoundness.CompactArithmetic
