import PASoundness.PAtoCompactAddTermBody
import PASoundness.PAtoCompactVacuousUniversal

/-! Alpha-move the fixed output binder of the right-zero addition witness.
This is one capture-safe K step, not a full addition-existence theorem. -/
namespace PASoundness.PAtoCompactAdditionOutputAlpha

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactAddTermBody
open PASoundness.PAtoCompactVacuousUniversal

/-- The candidate output and allocated addition relation with fixed input
names. The candidate and addition private blocks may overlap. -/
def body (d c out : Nat) : Formula :=
  andF (domainAt d out) (addAt c 30 31 out)

/-- The concrete candidate template's private binders start at d+32. -/
theorem domain_binders_ge (d x w : Nat) (h : w ∈ (domainAt d x).binders) :
    d + 32 ≤ w := by
  have ht : (domainTemplate 0).binders ⊆ Finset.Icc 30 37 := by decide
  unfold domainAt at h
  rw [mapNames_binders] at h
  obtain ⟨z, hz, he⟩ := Finset.mem_image.mp h
  have hz' := ht hz
  simp only [Finset.mem_Icc] at hz'
  have hn : z ≠ 0 := by omega
  simp [oneMap, hn] at he
  omega

theorem source_not_binder (d c : Nat) (hd : 32 < d + 32) (hc : 32 < c + 2) :
    32 ∉ (body d c 32).binders := by
  intro h
  simp only [body, PAtoCompactTermGraphBinderRange.andF_binders, Finset.mem_union] at h
  rcases h with h | h
  · have hb := domain_binders_ge d 32 32 h
    omega
  · have hb := addAt_private c 30 31 32 32 h
    omega

theorem target_not_names (d c out : Nat) (hlo : 32 < out)
    (hd : out < d + 32) (hc : out < c + 2) :
    out ∉ (body d c 32).names := by
  intro h
  rw [Formula.names_eq_free_union_binders] at h
  rcases Finset.mem_union.mp h with h | h
  · simp only [body, andF_free, Finset.mem_union] at h
    rcases h with h | h
    · have hh := domainAt_free d 32 h
      simp only [Finset.mem_singleton] at hh
      omega
    · have hh := addAt_free c 30 31 32 h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      omega
  · simp only [body, PAtoCompactTermGraphBinderRange.andF_binders, Finset.mem_union] at h
    rcases h with h | h
    · have hh := domain_binders_ge d 32 out h
      omega
    · have hh := addAt_private c 30 31 32 out h
      omega

theorem replace_body (d c out : Nat) (hd : 32 < d) (hc : 32 < c + 2) :
    replace 32 out (body d c 32) = body d c out := by
  rw [body, body]
  simp only [andF, Formula.not, replace]
  rw [replace_domainAt d 32 out hd, replace_addAt c 30 31 32 32 out hc]
  simp [rename]

/-- Move the output witness to an unused name. The bounds apply to
syntactic labels; the denoted objects may coincide. -/
def output_alpha (d c out : Nat) (hd : 32 < d) (hlo : 32 < out)
    (hdo : out < d + 32) (hco : out < c + 2) :
    KDerivation (imp (existsCode 32 (body d c 32).encode)
      (existsCode out (body d c out).encode)) ×
    KDerivation (imp (existsCode out (body d c out).encode)
      (existsCode 32 (body d c 32).encode)) := by
  have h := existentialAlpha 32 out (body d c 32) (by omega)
    (source_not_binder d c (by omega) (by omega))
    (target_not_names d c out hlo hdo hco)
  rw [replace_body d c out hd (by omega)] at h
  exact h

end PASoundness.PAtoCompactAdditionOutputAlpha

#print axioms PASoundness.PAtoCompactAdditionOutputAlpha.source_not_binder
#print axioms PASoundness.PAtoCompactAdditionOutputAlpha.domain_binders_ge
#print axioms PASoundness.PAtoCompactAdditionOutputAlpha.target_not_names
#print axioms PASoundness.PAtoCompactAdditionOutputAlpha.replace_body
#print axioms PASoundness.PAtoCompactAdditionOutputAlpha.output_alpha
