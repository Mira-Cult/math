import PASoundness.PAtoCompactGuardedOutputFormula

/-! Formula substitution with a shared term-graph output. Both replacement
terms keep their own graph at the same output name. Their guard-conditioned finite K graph-output
transport, guarded functionality and candidate-guard proofs are explicit
inputs. This module does not infer a shared witness from translated equality,
prove these graph laws, or use any semantic soundness theorem. -/

namespace PASoundness.PAtoCompactGuardedSharedValueFormulaSubst

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermSubstPolyReplacement PASoundness.PAtoCompactGuardedOutputFormula PASoundness.PAtoCompactGuardedOutputReplacement

/-- The guard and both term graphs are retained at the same output name. -/
def sharedGuard (g : Formula) (t u : Peano.Term) (q d : Nat) : Formula :=
  andF (retained g t q d) (termGraph id u q d)

/-- Given explicit graph laws and candidate projections for both terms,
their substitution instances agree in K under a shared graph output. This
works for arbitrary PA formulas, including nested quantifiers. -/
noncomputable def shared_value_substitution
    (g : Formula) (t u : Peano.Term) (x q d : Nat)
    (hqd : q < d)
    (htd : ∀ a ∈ t.varFinset, a < d)
    (hud : ∀ a ∈ u.varFinset, a < d)
    (htdom : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (hudom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (htout : GuardedOutputTransport g t) (htfunc : GuardFunctionality g t)
    (huout : GuardedOutputTransport g u) (hufunc : GuardFunctionality g u)
    (φ : Peano.Formula) :
    KDerivation (imp (sharedGuard g t u q d).encode
      (imp (code (FOL.substAt φ x t)) (code (FOL.substAt φ x u)))) := by
  let H := sharedGuard g t u q d
  let T := (formula (FOL.substAt φ x t)).encode
  let U := (formula (FOL.substAt φ x u)).encode
  let V := (formula (FOL.substAt φ x (.var q))).encode
  have ht := formula_replacement_substitution g t x q d hqd htd htdom htout htfunc φ
  have hu := formula_replacement_substitution g u x q d hqd hud hudom huout hufunc φ
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [T, H.encode]
  have hT : Context Γ T := Context.head _ _
  have hH : Context Γ H.encode := .hypothesis (by simp [Γ])
  have hparts : Context Γ (both (retained g t q d).encode (termGraph id u q d).encode) := by
    simpa [H, sharedGuard, andF, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using hH
  have hretT : Context Γ (retained g t q d).encode := Context.conjunctionLeft hparts
  have hgraphU : Context Γ (termGraph id u q d).encode := Context.conjunctionRight hparts
  have hretTparts : Context Γ (both g.encode (termGraph id t q d).encode) := by
    simpa [retained, andF, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using hretT
  have hg : Context Γ g.encode := Context.conjunctionLeft hretTparts
  have hretU : Context Γ (retained g u q d).encode := by
    have hh := Context.conjunctionIntro hg hgraphU
    simpa [retained, andF, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using hh
  have hV : Context Γ V := .mp hT (.mp hretT (.closed ht.2))
  have hU : Context Γ U := .mp hV (.mp hretU (.closed hu.1))
  exact hU

theorem shared_value_substitution_certificate
    (g : Formula) (t u : Peano.Term) (x q d : Nat)
    (hqd : q < d)
    (htd : ∀ a ∈ t.varFinset, a < d)
    (hud : ∀ a ∈ u.varFinset, a < d)
    (htdom : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (hudom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (htout : GuardedOutputTransport g t) (htfunc : GuardFunctionality g t)
    (huout : GuardedOutputTransport g u) (hufunc : GuardFunctionality g u)
    (φ : Peano.Formula) :
    theoremCode (certificate (shared_value_substitution g t u x q d hqd htd hud
      htdom hudom htout htfunc huout hufunc φ)) =
      imp (sharedGuard g t u q d).encode
        (imp (code (FOL.substAt φ x t)) (code (FOL.substAt φ x u))) :=
  certificate_correct _

end PASoundness.PAtoCompactGuardedSharedValueFormulaSubst

#print axioms PASoundness.PAtoCompactGuardedSharedValueFormulaSubst.sharedGuard
#print axioms PASoundness.PAtoCompactGuardedSharedValueFormulaSubst.shared_value_substitution
#print axioms PASoundness.PAtoCompactGuardedSharedValueFormulaSubst.shared_value_substitution_certificate
