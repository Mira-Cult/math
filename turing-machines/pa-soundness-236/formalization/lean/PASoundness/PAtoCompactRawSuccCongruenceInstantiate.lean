import PASoundness.PAtoCompactDynamicTransInstantiate
import PASoundness.PAtoCompactSuccessorCongruence

/-! Capture-safe instantiation of a four-operand raw-successor congruence
frame. The initial finite K proof is an explicit input. -/
namespace PASoundness.PAtoCompactRawSuccCongruenceInstantiate

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactTemplateBlockShift PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactTransitiveSuccessor

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Separate allocator blocks for quotient equivalence and for raw successor
and transitivity witnesses. The raw transitivity premises are explicit. -/
def frame (d e x y s t : Nat) : Formula :=
  .imp (equivAt e x y) (.imp (namedSuccessor x s (d+2))
    (.imp (namedSuccessor y t (d+3)) (.imp (namedTransitive x (d+4) (d+5))
      (.imp (namedTransitive y (d+4) (d+5)) (equivAt e s t)))))

theorem frame_not_binder (d e x y s t a : Nat) (hd : a < d+2) (he : a < e+2) :
    a ∉ (frame d e x y s t).binders := by
  simp only [frame, Formula.binders, Finset.mem_union, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have := equivAt_private e x y a h; omega
  · simp [namedSuccessor, namedSuccessorBody, namedBoth, namedEither, Formula.binders]; omega
  · simp [namedSuccessor, namedSuccessorBody, namedBoth, namedEither, Formula.binders]; omega
  · simp [namedTransitive, transitiveBody, Formula.binders]; omega
  · simp [namedTransitive, transitiveBody, Formula.binders]; omega
  · intro h; have := equivAt_private e s t a h; omega

theorem frame_replace (d e x y s t a b : Nat) (hd : a < d) (he : a < e) :
    replace a b (frame d e x y s t) = frame d e (rename a b x) (rename a b y)
      (rename a b s) (rename a b t) := by
  have eq1 : a ∉ (equivAt e x y).binders := by intro h; have := equivAt_private e x y a h; omega
  have eq2 : a ∉ (equivAt e s t).binders := by intro h; have := equivAt_private e s t a h; omega
  have hs : ∀ i < 64, rename a b (e+i) = e+i := by
    intro i hi
    simp [rename, show e+i ≠ a by omega]
  have h1 : replace a b (equivAt e x y) = equivAt e (rename a b x) (rename a b y) := by
    rw [← map_eq_replace a b _ eq1]
    exact equivAt_shift _ e e x y hs
  have h2 : replace a b (equivAt e s t) = equivAt e (rename a b s) (rename a b t) := by
    rw [← map_eq_replace a b _ eq2]
    exact equivAt_shift _ e e s t hs
  simp [frame, replace, h1, h2, namedSuccessor, namedSuccessorBody, namedBoth,
    namedEither, namedTransitive, transitiveBody, rename,
    show d+2 ≠ a by omega, show d+3 ≠ a by omega,
    show d+4 ≠ a by omega, show d+5 ≠ a by omega]

/-- Instantiate one source operand with a possibly existing target name. -/
def instantiate_name (d e x y s t a b : Nat) (hd : a < d) (he : a < e)
    (hbd : b < d+2) (hbe : b < e+2)
    (h : KDerivation (frame d e x y s t).encode) :
    KDerivation (frame d e (rename a b x) (rename a b y) (rename a b s) (rename a b t)).encode := by
  by_cases hab : a=b
  · subst b
    have hn : ∀ n, rename a a n = n := by intro n; simp [rename, eq_comm]
    simpa only [hn] using h
  · have hg : KDerivation (allCode a (frame d e x y s t).encode) := .generalize a h
    have hi := universalInstance a b (frame d e x y s t) hab
      (frame_not_binder d e x y s t a (by omega) (by omega))
      (frame_not_binder d e x y s t b hbd hbe)
    rw [frame_replace d e x y s t a b hd he] at hi
    exact .mp hg hi

/-- Fresh temporary names allow simultaneous substitution of four arbitrary
operands, including any identification of their target names. -/
def instantiate_frame (d e x y s t q : Nat)
    (hq : max (max (max (max 8 x) y) s) t < q)
    (hd : q+3 < d) (he : q+3 < e)
    (h : KDerivation (frame d e 0 1 7 8).encode) :
    KDerivation (frame d e x y s t).encode := by
  have h1 := instantiate_name d e 0 1 7 8 0 q (by omega) (by omega) (by omega) (by omega) h
  have h1' : KDerivation (frame d e q 1 7 8).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff] using h1
  have h2 := instantiate_name d e q 1 7 8 1 (q+1) (by omega) (by omega) (by omega) (by omega) h1'
  have h2' : KDerivation (frame d e q (q+1) 7 8).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff, show q ≠ 1 by omega] using h2
  have h3 := instantiate_name d e q (q+1) 7 8 7 (q+2) (by omega) (by omega) (by omega) (by omega) h2'
  have h3' : KDerivation (frame d e q (q+1) (q+2) 8).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff,
      show q ≠ 7 by omega, show q+1 ≠ 7 by omega] using h3
  have h4 := instantiate_name d e q (q+1) (q+2) 8 8 (q+3) (by omega) (by omega) (by omega) (by omega) h3'
  have h4' : KDerivation (frame d e q (q+1) (q+2) (q+3)).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff,
      show q ≠ 8 by omega, show q+1 ≠ 8 by omega, show q+2 ≠ 8 by omega] using h4
  have h5 := instantiate_name d e q (q+1) (q+2) (q+3) q x (by omega) (by omega) (by omega) (by omega) h4'
  have h5' : KDerivation (frame d e x (q+1) (q+2) (q+3)).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff,
      show q+1 ≠ q by omega, show q+2 ≠ q by omega, show q+3 ≠ q by omega] using h5
  have h6 := instantiate_name d e x (q+1) (q+2) (q+3) (q+1) y (by omega) (by omega) (by omega) (by omega) h5'
  have h6' : KDerivation (frame d e x y (q+2) (q+3)).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff,
      show x ≠ q+1 by omega, show q+2 ≠ q+1 by omega, show q+3 ≠ q+1 by omega] using h6
  have h7 := instantiate_name d e x y (q+2) (q+3) (q+2) s (by omega) (by omega) (by omega) (by omega) h6'
  have h7' : KDerivation (frame d e x y s (q+3)).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff,
      show x ≠ q+2 by omega, show y ≠ q+2 by omega, show q+3 ≠ q+2 by omega] using h7
  have h8 := instantiate_name d e x y s (q+3) (q+3) t (by omega) (by omega) (by omega) (by omega) h7'
  simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff,
    show x ≠ q+3 by omega, show y ≠ q+3 by omega, show s ≠ q+3 by omega] using h8

#print axioms instantiate_name
#print axioms instantiate_frame

end PASoundness.PAtoCompactRawSuccCongruenceInstantiate
