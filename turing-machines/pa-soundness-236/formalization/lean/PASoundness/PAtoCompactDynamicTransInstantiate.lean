import PASoundness.PAtoCompactCandidateDynamicReflexivity

/-! Capture-safe instantiation of an already derived candidate-relative
transitivity implication. This module constructs finite K proofs; the source
transitivity proof is an explicit input. -/
namespace PASoundness.PAtoCompactDynamicTransInstantiate

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactTemplateBlockShift PASoundness.PAtoCompactAlphaMapOne

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def frame (d e x y z : Nat) : Formula :=
  .imp (domainAt d x) (.imp (equivAt e x y) (.imp (equivAt e y z) (equivAt e x z)))

theorem frame_not_binder (d e x y z a : Nat) (hd : a < d + 2) (he : a < e + 2) :
    a ∉ (frame d e x y z).binders := by
  intro h
  simp only [frame, Formula.binders, Finset.mem_union] at h
  rcases h with h | h | h | h
  · have := domainAt_private d x a h; omega
  · have := equivAt_private e x y a h; omega
  · have := equivAt_private e y z a h; omega
  · have := equivAt_private e x z a h; omega

theorem frame_replace (d e x y z a b : Nat) (hd : a < d) (he : a < e) :
    replace a b (frame d e x y z) = frame d e (rename a b x) (rename a b y) (rename a b z) := by
  have hd' : a ∉ (domainAt d x).binders := by
    intro h; have := domainAt_private d x a h; omega
  have he' : a ∉ (equivAt e x y).binders := by
    intro h; have := equivAt_private e x y a h; omega
  have he'' : a ∉ (equivAt e y z).binders := by
    intro h; have := equivAt_private e y z a h; omega
  have he''' : a ∉ (equivAt e x z).binders := by
    intro h; have := equivAt_private e x z a h; omega
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
  have heq2 : replace a b (equivAt e y z) = equivAt e (rename a b y) (rename a b z) := by
    rw [← map_eq_replace a b _ he'']
    exact equivAt_shift _ e e y z hs2
  have heq3 : replace a b (equivAt e x z) = equivAt e (rename a b x) (rename a b z) := by
    rw [← map_eq_replace a b _ he''']
    exact equivAt_shift _ e e x z hs2
  simp only [frame, replace, hdom, heq1, heq2, heq3]

/-- Reassign one free operand name below the private-binder blocks.
The result may identify two operand names. -/
def instantiate_name (d e x y z a b : Nat) (hd : a < d) (he : a < e)
    (hbd : b < d + 2) (hbe : b < e + 2)
    (h : KDerivation (frame d e x y z).encode) :
    KDerivation (frame d e (rename a b x) (rename a b y) (rename a b z)).encode := by
  by_cases hab : a = b
  · subst b
    have hname : ∀ n, rename a a n = n := by
      intro n
      simp [rename, eq_comm]
    simpa only [hname] using h
  · have hg : KDerivation (allCode a (frame d e x y z).encode) := .generalize a h
    have hi := universalInstance a b (frame d e x y z) hab
      (frame_not_binder d e x y z a (by omega) (by omega))
      (frame_not_binder d e x y z b hbd hbe)
    rw [frame_replace d e x y z a b hd he] at hi
    exact .mp hg hi


/-- Apply a fresh-name permutation followed by identification. Inputs may alias. -/
def instantiate_frame (d e x y z q : Nat)
    (hq : max (max (max 8 x) y) z < q)
    (hd : q+2 < d) (he : q+2 < e)
    (h : KDerivation (frame d e 0 1 8).encode) : KDerivation (frame d e x y z).encode := by
  have h1 := instantiate_name d e 0 1 8 0 q (by omega) (by omega) (by omega) (by omega) h
  have h1' : KDerivation (frame d e q 1 8).encode := by simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff] using h1
  have h2 := instantiate_name d e q 1 8 1 (q+1) (by omega) (by omega) (by omega) (by omega) h1'
  have h2' : KDerivation (frame d e q (q+1) 8).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff, show q ≠ 1 by omega] using h2
  have h3 := instantiate_name d e q (q+1) 8 8 (q+2) (by omega) (by omega) (by omega) (by omega) h2'
  have h3' : KDerivation (frame d e q (q+1) (q+2)).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff, show q ≠ 8 by omega, show q+1 ≠ 8 by omega] using h3
  have h4 := instantiate_name d e q (q+1) (q+2) q x (by omega) (by omega) (by omega) (by omega) h3'
  have h4' : KDerivation (frame d e x (q+1) (q+2)).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff, show q+1 ≠ q by omega, show q+2 ≠ q by omega] using h4
  have h5 := instantiate_name d e x (q+1) (q+2) (q+1) y (by omega) (by omega) (by omega) (by omega) h4'
  have h5' : KDerivation (frame d e x y (q+2)).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff, show x ≠ q+1 by omega, show q+2 ≠ q+1 by omega] using h5
  have h6 := instantiate_name d e x y (q+2) (q+2) z (by omega) (by omega) (by omega) (by omega) h5'
  simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff, show x ≠ q+2 by omega, show y ≠ q+2 by omega] using h6

#print axioms instantiate_name
#print axioms instantiate_frame
end PASoundness.PAtoCompactDynamicTransInstantiate
