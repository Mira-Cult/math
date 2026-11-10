import PASoundness.PAtoCompactSuccInjectivityGuardedFrame
import PASoundness.PAtoCompactGuardedVacuity

/-! Canonical allocation for the conditional guarded PA successor-injectivity
frame adapter. The displayed matrix derivation remains an explicit K proof input. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccInjectivityCanonicalFrame

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedVacuity
open PASoundness.PAtoCompactSuccInjectivityGuardedFrame

/-- Every variable of either operand occurs in the PA axiom. -/
theorem operand_vars_in_axiom (t u : Peano.Term) :
    t.varFinset ⊆ (succInjective t u).freeVarFinset ∧
    u.varFinset ⊆ (succInjective t u).freeVarFinset := by
  constructor <;> intro a ha <;>
    simp [succInjective, BoundedFormula.freeVarFinset, eq_free, ha]

/-- The axiom's standard guard base bounds every operand and guard free name. -/
theorem canonical_bounds (t u : Peano.Term) :
    (∀ a ∈ t.varFinset, a < guardBase (succInjective t u)) ∧
    (∀ a ∈ u.varFinset, a < guardBase (succInjective t u)) ∧
    (∀ a ∈ (guardFormula (succInjective t u)).free, a < guardBase (succInjective t u)) := by
  have ht := (operand_vars_in_axiom t u).1
  have hu := (operand_vars_in_axiom t u).2
  have hg := guardFormula_free_subset (succInjective t u)
  constructor
  · intro a ha
    have h := Finset.le_sup (f := id) (ht ha)
    simp only [id_eq] at h
    unfold guardBase
    omega
  constructor
  · intro a ha
    have h := Finset.le_sup (f := id) (hu ha)
    simp only [id_eq] at h
    unfold guardBase
    omega
  · intro a ha
    have h := Finset.le_sup (f := id) (hg ha)
    simp only [id_eq] at h
    unfold guardBase
    omega

/-- The PA axiom follows from the actual pointwise K proof at its canonical
base; no caller-provided name-bound hypotheses remain. -/
noncomputable def guarded_of_canonical_matrix (t u : Peano.Term)
    (pointwise :
      let base := guardBase (succInjective t u)
      KDerivation (imp (guardFormula (succInjective t u)).encode
        (imp (matrix id (Peano.succ t) (Peano.succ u) base (base+1) (base+2)
          (base+2+termCost (Peano.succ t))
          (base+2+termCost (Peano.succ t)+termCost (Peano.succ u))).encode
          (equalityFrame id t u base).encode))) :
    KDerivation (guardedCode (succInjective t u)) := by
  have h := canonical_bounds t u
  exact guarded_of_matrix t u _ h.1 h.2.1 h.2.2 pointwise

theorem guarded_of_canonical_matrix_certificate (t u : Peano.Term)
    (pointwise :
      let base := guardBase (succInjective t u)
      KDerivation (imp (guardFormula (succInjective t u)).encode
        (imp (matrix id (Peano.succ t) (Peano.succ u) base (base+1) (base+2)
          (base+2+termCost (Peano.succ t))
          (base+2+termCost (Peano.succ t)+termCost (Peano.succ u))).encode
          (equalityFrame id t u base).encode))) :
    theoremCode (certificate (guarded_of_canonical_matrix t u pointwise)) =
      guardedCode (succInjective t u) := certificate_correct _

end PASoundness.PAtoCompactSuccInjectivityCanonicalFrame

#print axioms PASoundness.PAtoCompactSuccInjectivityCanonicalFrame.operand_vars_in_axiom
#print axioms PASoundness.PAtoCompactSuccInjectivityCanonicalFrame.canonical_bounds
#print axioms PASoundness.PAtoCompactSuccInjectivityCanonicalFrame.guarded_of_canonical_matrix
#print axioms PASoundness.PAtoCompactSuccInjectivityCanonicalFrame.guarded_of_canonical_matrix_certificate
