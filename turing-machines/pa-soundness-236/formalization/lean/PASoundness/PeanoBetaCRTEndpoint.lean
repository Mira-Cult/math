import PASoundness.PeanoBetaCRTStepClosed
import PASoundness.PeanoBetaCRTGuardedInduction
/-! Bounded CRT endpoint in the PA calculus, conditional on explicit bounded
residue totality and ordered-pair inverse formulas. This does not construct a
suitable parameter or prove beta-trace existence. -/
namespace PASoundness.PeanoBetaCRTEndpoint
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaCRTInvariant PeanoBetaCRTAlignment
private theorem fv_inf (φ ψ : Peano.Formula) :
    (φ ⊓ ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  change ((φ.imp ψ.not).not).freeVarFinset = _
  simp [FirstOrder.Language.BoundedFormula.freeVarFinset]
private theorem fv_exists (φ : Peano.Formula) (x : Nat) :
    (FOL.existsAt x φ).freeVarFinset = φ.freeVarFinset.erase x := by
  simp [FOL.existsAt, SyntaxTransport.allAt_freeVars,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]

def global (φ : Peano.Formula) : Peano.Formula :=
  PeanoBetaCRTResidueSelect.totality φ ⊓ PeanoBetaCRTFuturePair.endpointAt8

theorem totality_fresh7 (φ : Peano.Formula) (hφ : 7 ∉ φ.freeVarFinset) :
    7 ∉ (PeanoBetaCRTResidueSelect.totality φ).freeVarFinset := by
  have h1 : (less (.var 2) (.var 8)).freeVarFinset = {2,8} := by decide
  have h2 : (less (.var 3) (modulus (.var 1) (.var 2))).freeVarFinset = {1,2,3} := by decide
  simp [PeanoBetaCRTResidueSelect.totality, fv_inf, fv_exists,
    SyntaxTransport.allAt_freeVars, FirstOrder.Language.BoundedFormula.freeVarFinset,
    h1, h2, hφ]

theorem global_fresh7 (φ : Peano.Formula) (hφ : 7 ∉ φ.freeVarFinset) :
    7 ∉ (global φ).freeVarFinset := by
  have he : 7 ∉ PeanoBetaCRTFuturePair.endpointAt8.freeVarFinset :=
    PeanoBetaCRTFuturePair.endpoint_fresh 7 (by decide) (by decide)
  simpa [global, fv_inf] using And.intro (totality_fresh7 φ hφ) he
open PeanoDivisibility
private theorem subst_imp (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ.imp ψ) x t = (FOL.substAt φ x t).imp (FOL.substAt ψ x t) := rfl
private theorem subst_not (φ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt φ.not x t = (FOL.substAt φ x t).not := rfl
private theorem subst_and (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ ⊓ ψ) x t = (FOL.substAt φ x t) ⊓ (FOL.substAt ψ x t) := rfl
private theorem lt_bound_sub : FOL.substAt (less (.var 2) (.var 7)) 7 (.var 8) = less (.var 2) (.var 8) := by
  simp [FOL.substAt, less_subst, FirstOrder.Language.Term.subst]

private theorem lt_upper_fresh : FOL.substAt (less (.var 2) (.var 8)) 7 (.var 8) = less (.var 2) (.var 8) := by
  apply PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh
  decide

private theorem row_beta_bound_fresh : FOL.substAt
    (beta (.var 9) (.var 1) (.var 2) (.var 3)) 7 (.var 8) =
    beta (.var 9) (.var 1) (.var 2) (.var 3) := by
  apply PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh
  decide

private theorem factor_bound_fresh : FOL.substAt
    (divides (modulus (.var 1) (.var 2)) (.var 10)) 7 (.var 8) =
    divides (modulus (.var 1) (.var 2)) (.var 10) := by
  apply PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh
  decide

private theorem inv_bound_fresh : FOL.substAt
    ((mul (.var 10) (.var 3)).equal
      (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2))))) 7 (.var 8) =
    ((mul (.var 10) (.var 3)).equal
      (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2))))) := by
  apply PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh
  decide

theorem rows_bound (φ : Peano.Formula) (hφ : 7 ∉ φ.freeVarFinset) :
    FOL.substAt (rowsAt φ (.var 7) 9) 7 (.var 8) = rowsAt φ (.var 8) 9 := by
  unfold rowsAt
  rw [PeanoBetaCRTAlpha.subst_var_allAt _ 7 8 2 (by decide) (by decide), subst_imp, lt_bound_sub,
    PeanoBetaCRTAlpha.subst_var_existsAt _ 7 8 3 (by decide) (by decide), subst_and,
    PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh φ 7 (.var 8) hφ, row_beta_bound_fresh]

theorem factors_bound : FOL.substAt (factorsAt (.var 7) 10) 7 (.var 8) = factorsAt (.var 8) 10 := by
  unfold factorsAt
  rw [PeanoBetaCRTAlpha.subst_var_allAt _ 7 8 2 (by decide) (by decide), subst_imp, lt_bound_sub, factor_bound_fresh]

theorem future_bound : FOL.substAt (futureAt (.var 7) 10) 7 (.var 8) = futureAt (.var 8) 10 := by
  unfold futureAt
  rw [PeanoBetaCRTAlpha.subst_var_allAt _ 7 8 2 (by decide) (by decide), subst_imp, subst_and, subst_not, lt_bound_sub, lt_upper_fresh,
    PeanoBetaCRTAlpha.subst_var_existsAt _ 7 8 3 (by decide) (by decide), PeanoBetaCRTAlpha.subst_var_existsAt _ 7 8 4 (by decide) (by decide), inv_bound_fresh]

theorem matrix_bound (φ : Peano.Formula) (hφ : 7 ∉ φ.freeVarFinset) :
    FOL.substAt (matrixAt φ (.var 7) 9 10) 7 (.var 8) = matrixAt φ (.var 8) 9 10 := by
  unfold matrixAt
  rw [subst_and, subst_and, rows_bound φ hφ, factors_bound, future_bound]

theorem invariant_bound (φ : Peano.Formula) (hφ : 7 ∉ φ.freeVarFinset) :
    FOL.substAt (invariantAt φ (.var 7)) 7 (.var 8) = invariantAt φ (.var 8) := by
  unfold invariantAt invariantWith
  rw [PeanoBetaCRTAlpha.subst_var_existsAt _ 7 8 10 (by decide) (by decide), PeanoBetaCRTAlpha.subst_var_existsAt _ 7 8 9 (by decide) (by decide), matrix_bound φ hφ]



/-- The concrete reviewed step supplies the guarded-induction step under the
global residue-totality and endpoint-pair hypotheses. -/
theorem step_from_global (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FormulaProves ((global φ).imp ((less (.var 7) (.var 8)).imp
      ((currentInvariant φ).imp (FOL.substAt (currentInvariant φ) 7 (succ (.var 7)))))) := by
  let G := global φ
  let L := less (.var 7) (.var 8)
  let I := currentInvariant φ
  let Γ := [I,L,G]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hg : FOL.Context Peano.Axiom Γ G := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ L := .hypothesis (by simp [Γ])
  have hi : FOL.Context Peano.Axiom Γ I := FOL.Context.head _ _
  have ht : FOL.Context Peano.Axiom Γ (PeanoBetaCRTResidueSelect.totality φ) :=
    FOL.Context.conjunctionLeft hg
  have he : FOL.Context Peano.Axiom Γ PeanoBetaCRTFuturePair.endpointAt8 :=
    FOL.Context.conjunctionRight hg
  have hs : FOL.Context Peano.Axiom Γ (PeanoBetaCRTStepClosed.side φ) :=
    FOL.Context.conjunctionIntro (FOL.Context.conjunctionIntro ht hl) he
  exact .mp (.mp (.closed (PeanoBetaCRTStepClosed.literal_successor φ hφ)) hs) hi

/-- PA proves the bounded CRT invariant at N from explicit global residue
and ordered-pair inverse assumptions. The result is conditional on those
object-level formulas; it does not construct C, a power trace, or a PA bridge. -/
theorem conditional_endpoint (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FormulaProves ((global φ).imp (invariantAt φ (.var 8))) := by
  have fresh (x : Nat) (hx : x ∈ reservedNames) : x ∉ φ.freeVarFinset := by
    intro h; exact hφ x h hx
  have h7 := fresh 7 (by simp [reservedNames])
  have h9 := fresh 9 (by simp [reservedNames])
  have h10 := fresh 10 (by simp [reservedNames])
  have h := PeanoBetaCRTGuardedInduction.guarded_endpoint φ (global φ)
    h7 h9 h10 (global_fresh7 φ h7) (step_from_global φ hφ)
  simpa only [currentInvariant, invariant_bound φ h7] using h

end PASoundness.PeanoBetaCRTEndpoint
