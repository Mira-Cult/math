import PASoundness.PAtoCompactCandidateDynamicReflexivity

/-! Capture-safe instantiation of an already derived candidate-relative
symmetry implication. This module constructs finite K proofs; the source
symmetry proof is an explicit input. -/
namespace PASoundness.PAtoCompactDynamicSymmetryInstantiate

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactTemplateBlockShift PASoundness.PAtoCompactAlphaMapOne

set_option maxRecDepth 65536
set_option maxHeartbeats 200000

def frame (d e x y : Nat) : Formula :=
  .imp (domainAt d x) (.imp (equivAt e x y) (equivAt e y x))

theorem frame_not_binder (d e x y a : Nat) (hd : a < d + 2) (he : a < e + 2) :
    a ∉ (frame d e x y).binders := by
  intro h
  simp only [frame, Formula.binders, Finset.mem_union] at h
  rcases h with h | h | h
  · have := domainAt_private d x a h; omega
  · have := equivAt_private e x y a h; omega
  · have := equivAt_private e y x a h; omega

theorem frame_replace (d e x y a b : Nat) (hd : a < d) (he : a < e) :
    replace a b (frame d e x y) = frame d e (rename a b x) (rename a b y) := by
  have hd' : a ∉ (domainAt d x).binders := by
    intro h; have := domainAt_private d x a h; omega
  have he' : a ∉ (equivAt e x y).binders := by
    intro h; have := equivAt_private e x y a h; omega
  have he'' : a ∉ (equivAt e y x).binders := by
    intro h; have := equivAt_private e y x a h; omega
  have hs1 : ∀ i < 64, rename a b (d + i) = d + i := by
    intro i hi
    have h : d+i ≠ a := by omega
    simp [rename, h]
  have hs2 : ∀ i < 64, rename a b (e + i) = e + i := by
    intro i hi
    have h : e+i ≠ a := by omega
    simp [rename, h]
  have hdom : replace a b (domainAt d x) = domainAt d (rename a b x) := by
    rw [← map_eq_replace a b _ hd']
    exact domainAt_shift _ d d x hs1
  have heq1 : replace a b (equivAt e x y) = equivAt e (rename a b x) (rename a b y) := by
    rw [← map_eq_replace a b _ he']
    exact equivAt_shift _ e e x y hs2
  have heq2 : replace a b (equivAt e y x) = equivAt e (rename a b y) (rename a b x) := by
    rw [← map_eq_replace a b _ he'']
    exact equivAt_shift _ e e y x hs2
  change Formula.imp (replace a b (domainAt d x))
    (.imp (replace a b (equivAt e x y)) (replace a b (equivAt e y x))) = _
  rw [hdom, heq1, heq2]
  rfl

/-- Reassign one free operand name while keeping source and target names
below the private binder blocks. The result may identify two operand names. -/
def instantiate_name (d e x y a b : Nat) (hd : a < d) (he : a < e)
    (hbd : b < d + 2) (hbe : b < e + 2)
    (h : KDerivation (frame d e x y).encode) :
    KDerivation (frame d e (rename a b x) (rename a b y)).encode := by
  by_cases hab : a = b
  · subst b
    have hx : rename a a x = x := by simp [rename, eq_comm]
    have hy : rename a a y = y := by simp [rename, eq_comm]
    rw [hx, hy]
    exact h
  · have hg : KDerivation (allCode a (frame d e x y).encode) := .generalize a h
    have hi := universalInstance a b (frame d e x y) hab
      (frame_not_binder d e x y a (by omega) (by omega))
      (frame_not_binder d e x y b hbd hbe)
    rw [frame_replace d e x y a b hd he] at hi
    exact .mp hg hi

/-- Instantiate both fixed names via a temporary name distinct from the
operands and source names. Output operand names may coincide. -/
def instantiate_frame (d e x y q : Nat)
    (hd : max (max (max 8 x) y) q < d) (he : max (max (max 8 x) y) q < e)
    (hq8 : q ≠ 8) (hq1 : q ≠ 1) (hqx : q ≠ x) (hqy : q ≠ y)
    (h : KDerivation (frame d e 8 1).encode) : KDerivation (frame d e x y).encode := by
  have h1 := instantiate_name d e 8 1 8 q (by omega) (by omega) (by omega) (by omega) h
  have hr18 : rename 8 q 8 = q := by simp [rename]
  have hr11 : rename 8 q 1 = 1 := by simp [rename]
  rw [hr18, hr11] at h1
  have h1' : KDerivation (frame d e q 1).encode := h1
  have h2 := instantiate_name d e q 1 1 y (by omega) (by omega) (by omega) (by omega) h1'
  have hr2q : rename 1 y q = q := by simp [rename, hq1]
  have hr21 : rename 1 y 1 = y := by simp [rename]
  rw [hr2q, hr21] at h2
  have h2' : KDerivation (frame d e q y).encode := h2
  have h3 := instantiate_name d e q y q x (by omega) (by omega) (by omega) (by omega) h2'
  have hr3q : rename q x q = x := by simp [rename]
  have hr3y : rename q x y = y := by simp [rename, Ne.symm hqy]
  rw [hr3q, hr3y] at h3
  exact h3

#print axioms instantiate_name
#print axioms instantiate_frame
end PASoundness.PAtoCompactDynamicSymmetryInstantiate
