import PASoundness.PAtoCompactGuardedEqualityMatrixSharedValue

/-! Pointwise equality-substitution under a translated equality matrix.
Guarded graph output-transport, guarded functionality and candidate-guard proofs
remain explicit. Existential elimination and those graph laws are separate
obligations. No semantic soundness theorem is used. -/

namespace PASoundness.PAtoCompactGuardedEqualityMatrixFormulaSubst

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactTermSubstPolyReplacement
open PASoundness.PAtoCompactGuardedOutputReplacement PASoundness.PAtoCompactGuardedSharedValueFormulaSubst PASoundness.PAtoCompactGuardedEqualityMatrixSharedValue

/-- Under the same guard, an actual equality matrix and the source
substitution instance yield the target substitution instance. The two graph
outputs are reconciled constructively through the supplied output transport. -/
noncomputable def matrix_formula_substitution
    (g : Formula) (t u : Peano.Term) (φ : Peano.Formula) (x w z p s e d : Nat)
    (hwp : w < p) (hwd : w < d) (hzs : z < s) (hzd : z < d)
    (hwe : w < e+2) (hze : z < e+2)
    (htp : ∀ a ∈ t.varFinset, a < p) (htd : ∀ a ∈ t.varFinset, a < d)
    (hus : ∀ a ∈ u.varFinset, a < s) (hud : ∀ a ∈ u.varFinset, a < d)
    (hgd : ∀ a ∈ g.free, a < d)
    (htdom : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (hudom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (htout : GuardedOutputTransport g t) (htfunc : GuardFunctionality g t)
    (huout : GuardedOutputTransport g u) (hufunc : GuardFunctionality g u) :
    KDerivation (imp g.encode (imp (matrix id t u w z p s e).encode
      (imp (code (FOL.substAt φ x t)) (code (FOL.substAt φ x u))))) := by
  have hs := matrix_to_shared g t u w z p s e d hwp hwd hzs hzd hwe hze htp htd hus hud hgd hudom huout
  have hf := shared_value_substitution g t u x w d hwd htd hud
    htdom hudom htout htfunc huout hufunc φ
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let M := (matrix id t u w z p s e).encode
  let T := code (FOL.substAt φ x t)
  let Γ := [T, M, g.encode]
  have hT : Context Γ T := Context.head _ _
  have hM : Context Γ M := .hypothesis (by simp [Γ])
  have hG : Context Γ g.encode := .hypothesis (by simp [Γ])
  have hshared : Context Γ (sharedGuard g t u w d).encode := .mp hM (.mp hG (.closed hs))
  exact .mp hT (.mp hshared (.closed hf))

theorem matrix_formula_substitution_certificate
    (g : Formula) (t u : Peano.Term) (φ : Peano.Formula) (x w z p s e d : Nat)
    (hwp : w < p) (hwd : w < d) (hzs : z < s) (hzd : z < d)
    (hwe : w < e+2) (hze : z < e+2)
    (htp : ∀ a ∈ t.varFinset, a < p) (htd : ∀ a ∈ t.varFinset, a < d)
    (hus : ∀ a ∈ u.varFinset, a < s) (hud : ∀ a ∈ u.varFinset, a < d)
    (hgd : ∀ a ∈ g.free, a < d)
    (htdom : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (hudom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (htout : GuardedOutputTransport g t) (htfunc : GuardFunctionality g t)
    (huout : GuardedOutputTransport g u) (hufunc : GuardFunctionality g u) :
    theoremCode (certificate (matrix_formula_substitution g t u φ x w z p s e d
      hwp hwd hzs hzd hwe hze htp htd hus hud hgd htdom hudom htout htfunc huout hufunc)) =
      imp g.encode (imp (matrix id t u w z p s e).encode
        (imp (code (FOL.substAt φ x t)) (code (FOL.substAt φ x u)))) :=
  certificate_correct _

end PASoundness.PAtoCompactGuardedEqualityMatrixFormulaSubst

#print axioms PASoundness.PAtoCompactGuardedEqualityMatrixFormulaSubst.matrix_formula_substitution
#print axioms PASoundness.PAtoCompactGuardedEqualityMatrixFormulaSubst.matrix_formula_substitution_certificate
