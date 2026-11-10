import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactGuardedAllElim
import PASoundness.PAtoCompactDirectGeneralization
import PASoundness.PAtoCompactVacuousUniversal

/-! A capture-safe variable instance from explicit low-target active-name
alignment. The source-specific alignment with PA substitution remains separate. -/
namespace PASoundness.PAtoCompactAllElimVariableInstance

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactVacuousQuantifierFree
open PASoundness.PAtoCompactScopedActiveReplace
open FirstOrder FirstOrder.Language
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactVacuousUniversal PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactScopedActiveAll
open PASoundness.PAtoCompactGuardedAllElim PASoundness.PAtoCompactDirectGeneralization
open PASoundness.PAtoCompactGuardedAllImpAlignment
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactGuardedAllImp
open PASoundness.CompactHilbertBasis

set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-- Every generated binder is greater than every active name, including
names strictly below an active one. -/
theorem below_active_not_binder {n : Nat} (φ : Peano.language.BoundedFormula Nat n) :
    ∀ (bound : Fin n → Nat) (i : Fin n) (v : Nat), v ≤ bound i →
      v ∉ (scopedFormula n φ bound).binders := by
  induction φ with
  | falsum => intro bound i v hv; simp [scopedFormula, Formula.binders]
  | @equal n t u =>
      intro bound i v hv h
      rw [scoped_equal_frame] at h
      have hge := equalityFrame_binders_ge (Sum.elim id bound) t u
        (scopeBase (.equal t u) bound) v h
      have hlt := bound_lt_scopeBase (.equal t u) bound i
      omega
  | rel r ts => exact nomatch r
  | imp a b iha ihb =>
      intro bound i v hv h
      simp only [scopedFormula, Formula.binders, Finset.mem_union] at h
      cases h with
      | inl h => exact iha bound i v hv h
      | inr h => exact ihb bound i v hv h
  | @all n body ih =>
      intro bound i v hv h
      let z := scopeBase (.all body) bound
      have hlt : bound i < z := bound_lt_scopeBase (.all body) bound i
      change v ∈ (Formula.all z (.imp (domainAt (z+1) z)
        (scopedFormula (n+1) body (Fin.snoc bound z)))).binders at h
      simp only [Formula.binders, Finset.mem_insert, Finset.mem_union] at h
      rcases h with he | hd | hs
      · omega
      · have hp := domainAt_private (z+1) z v hd
        omega
      · have hn := ih (Fin.snoc bound z) (Fin.castSucc i) v (by simpa using hv)
        exact hn hs

/-- Specialization at an arbitrary, possibly already free source label.
The only remaining input is finite K alignment of the literal replacement
of the high active name with the scope generated using the target label. -/
noncomputable def instance_of_low_alignment (φ : Peano.Formula) (x y : Nat)
    (alignment : KBoth
      (replace (instanceBinder φ x y) y (scopeAt φ x (instanceBinder φ x y)))
      (scopeAt φ x y)) :
    KDerivation (imp (code (FOL.allAt x φ))
      (imp (domainAt (instanceBinder φ x y + 1) y).encode (scopeAt φ x y).encode)) := by
  let z := instanceBinder φ x y
  let T := scopeAt φ x z
  let M : Formula := .imp (domainAt (z+1) z) T
  have hzy : y < z := by dsimp [z, instanceBinder]; omega
  have htop : topName x φ < z := by
    have hh := ceiling_top φ x
    dsimp [z, instanceBinder]
    omega
  have hz : z ∉ (originalChild φ x).names := by
    intro hz
    have hh := ceiling_child φ x z hz
    dsimp [z, instanceBinder] at hh
    omega
  have hzT : z ∉ T.binders := by
    have hh := below_active_not_binder (allAtBody x φ) (Fin.snoc Fin.elim0 z)
      (Fin.last 0) z (by simp)
    simpa [T, scopeAt] using hh
  have hyT : y ∉ T.binders := by
    have hh := below_active_not_binder (allAtBody x φ) (Fin.snoc Fin.elim0 z)
      (Fin.last 0) y (by simp; omega)
    simpa [T, scopeAt] using hh
  have hzM : z ∉ M.binders := by
    simp only [M, Formula.binders, Finset.mem_union, not_or]
    exact ⟨by intro h; have := domainAt_private (z+1) z z h; omega, hzT⟩
  have hyM : y ∉ M.binders := by
    simp only [M, Formula.binders, Finset.mem_union, not_or]
    exact ⟨by intro h; have := domainAt_private (z+1) z y h; omega, hyT⟩
  have hi := universalInstance z y M (by omega) hzM hyM
  have hg : replace z y (domainAt (z+1) z) = domainAt (z+1) y := by
    simpa [rename] using replace_domain_guard (z+1) z z y (by omega)
  have hi' : KDerivation (imp (Formula.all z M).encode
      (imp (domainAt (z+1) y).encode (replace z y T).encode)) := by
    simpa only [M, replace, hg, Formula.encode] using hi
  have ha := (align_at φ x z htop hz).1
  have hs := implicationCongr (identity (domainAt (z+1) y).encode) alignment.1
  exact compose ha (compose hi' hs)

#print axioms below_active_not_binder
#print axioms instance_of_low_alignment
end PASoundness.PAtoCompactAllElimVariableInstance
