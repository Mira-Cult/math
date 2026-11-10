import PASoundness.PAtoCompactRawSuccCongruenceInstantiate
import PASoundness.PAtoCompactSuccBaseMultiAlpha
import PASoundness.PAtoCompactEquivMultiAlpha

/-! Capture-safe instantiation of a quotient-successor cancellation frame.
The canonical-frame K derivation remains an explicit input: this file does
not construct cancellation itself. All four target operands may alias. -/
namespace PASoundness.PAtoCompactQuotSuccCancellationDynamicInstantiate
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactTemplateBlockShift PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactSuccBaseMultiAlpha PASoundness.PAtoCompactEquivMultiAlpha
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The four-operand cancellation shape with one private allocator. -/
def frame (b x y s t : Nat) : Formula :=
  .imp (succAt b x s) (.imp (succAt b y t)
    (.imp (equivAt b s t) (equivAt b x y)))

theorem frame_not_binder (b x y s t a : Nat) (ha : a < b+2) :
    a ∉ (frame b x y s t).binders := by
  simp only [frame, Formula.binders, Finset.mem_union, not_or]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; have := succAt_private b x s a h; omega
  · intro h; have := succAt_private b y t a h; omega
  · intro h; have := equivAt_private b s t a h; omega
  · intro h; have := equivAt_private b x y a h; omega

theorem frame_replace (b x y s t a v : Nat) (ha : a < b) :
    replace a v (frame b x y s t) = frame b (rename a v x) (rename a v y)
      (rename a v s) (rename a v t) := by
  have hs1 : a ∉ (succAt b x s).binders := by intro h; have := succAt_private b x s a h; omega
  have hs2 : a ∉ (succAt b y t).binders := by intro h; have := succAt_private b y t a h; omega
  have he1 : a ∉ (equivAt b s t).binders := by intro h; have := equivAt_private b s t a h; omega
  have he2 : a ∉ (equivAt b x y).binders := by intro h; have := equivAt_private b x y a h; omega
  have hb : ∀ i < 64, rename a v (b+i) = b+i := by
    intro i hi
    simp [rename, show b+i ≠ a by omega]
  have h1 : replace a v (succAt b x s) = succAt b (rename a v x) (rename a v s) := by
    rw [← map_eq_replace a v _ hs1]
    exact succAt_shift _ b b x s hb
  have h2 : replace a v (succAt b y t) = succAt b (rename a v y) (rename a v t) := by
    rw [← map_eq_replace a v _ hs2]
    exact succAt_shift _ b b y t hb
  have h3 : replace a v (equivAt b s t) = equivAt b (rename a v s) (rename a v t) := by
    rw [← map_eq_replace a v _ he1]
    exact equivAt_shift _ b b s t hb
  have h4 : replace a v (equivAt b x y) = equivAt b (rename a v x) (rename a v y) := by
    rw [← map_eq_replace a v _ he2]
    exact equivAt_shift _ b b x y hb
  simp only [frame, replace, h1, h2, h3, h4]

/-- Reassign one free operand without capture; the target may be an existing operand. -/
def instantiate_name (b x y s t a v : Nat) (ha : a < b) (hv : v < b+2)
    (h : KDerivation (frame b x y s t).encode) :
    KDerivation (frame b (rename a v x) (rename a v y) (rename a v s) (rename a v t)).encode := by
  by_cases hav : a=v
  · subst v
    have hn : ∀ n, rename a a n = n := by intro n; simp [rename, eq_comm]
    simpa only [hn] using h
  · have hg : KDerivation (allCode a (frame b x y s t).encode) := .generalize a h
    have hi := universalInstance a v (frame b x y s t) hav
      (frame_not_binder b x y s t a (by omega)) (frame_not_binder b x y s t v hv)
    rw [frame_replace b x y s t a v ha] at hi
    exact .mp hg hi

/-- Instantiate four canonical operands using fresh temporary names, permitting
arbitrary target aliases. The source proof is an explicit finite K input. -/
def instantiate_frame (b x y s t tmp : Nat)
    (htmp : max (max (max (max 8 x) y) s) t < tmp) (hb : tmp+3 < b)
    (h : KDerivation (frame b 0 1 7 8).encode) : KDerivation (frame b x y s t).encode := by
  have h1 := instantiate_name b 0 1 7 8 0 tmp (by omega) (by omega) h
  have h1' : KDerivation (frame b tmp 1 7 8).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff] using h1
  have h2 := instantiate_name b tmp 1 7 8 1 (tmp+1) (by omega) (by omega) h1'
  have h2' : KDerivation (frame b tmp (tmp+1) 7 8).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff, show tmp ≠ 1 by omega] using h2
  have h3 := instantiate_name b tmp (tmp+1) 7 8 7 (tmp+2) (by omega) (by omega) h2'
  have h3' : KDerivation (frame b tmp (tmp+1) (tmp+2) 8).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff,
      show tmp ≠ 7 by omega, show tmp+1 ≠ 7 by omega] using h3
  have h4 := instantiate_name b tmp (tmp+1) (tmp+2) 8 8 (tmp+3) (by omega) (by omega) h3'
  have h4' : KDerivation (frame b tmp (tmp+1) (tmp+2) (tmp+3)).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff,
      show tmp ≠ 8 by omega, show tmp+1 ≠ 8 by omega, show tmp+2 ≠ 8 by omega] using h4
  have h5 := instantiate_name b tmp (tmp+1) (tmp+2) (tmp+3) tmp x (by omega) (by omega) h4'
  have h5' : KDerivation (frame b x (tmp+1) (tmp+2) (tmp+3)).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff,
      show tmp+1 ≠ tmp by omega, show tmp+2 ≠ tmp by omega, show tmp+3 ≠ tmp by omega] using h5
  have h6 := instantiate_name b x (tmp+1) (tmp+2) (tmp+3) (tmp+1) y (by omega) (by omega) h5'
  have h6' : KDerivation (frame b x y (tmp+2) (tmp+3)).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff,
      show x ≠ tmp+1 by omega, show tmp+2 ≠ tmp+1 by omega, show tmp+3 ≠ tmp+1 by omega] using h6
  have h7 := instantiate_name b x y (tmp+2) (tmp+3) (tmp+2) s (by omega) (by omega) h6'
  have h7' : KDerivation (frame b x y s (tmp+3)).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff,
      show x ≠ tmp+2 by omega, show y ≠ tmp+2 by omega, show tmp+3 ≠ tmp+2 by omega] using h7
  have h8 := instantiate_name b x y s (tmp+3) (tmp+3) t (by omega) (by omega) h7'
  simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff,
    show x ≠ tmp+3 by omega, show y ≠ tmp+3 by omega, show s ≠ tmp+3 by omega] using h8

/-- Move the supplied cancellation frame between private blocks while retaining
the same four operand names. -/
def frame_base_alpha (b c x y s t : Nat)
    (hxb : x < b+2) (hyb : y < b+2) (hsb : s < b+2) (htb : t < b+2)
    (hxc : x < c+2) (hyc : y < c+2) (hsc : s < c+2) (htc : t < c+2) :
    ProofEquiv (frame b x y s t) (frame c x y s t) := by
  have h1 := succAt_base_alpha b c x s hxb hsb hxc hsc
  have h2 := succAt_base_alpha b c y t hyb htb hyc htc
  have h3 := equivAt_base_alpha b c s t hsb htb hsc htc
  have h4 := equivAt_base_alpha b c x y hxb hyb hxc hyc
  exact ProofEquiv.implication h1 (ProofEquiv.implication h2 (ProofEquiv.implication h3 h4))

/-- A canonical proof family at arbitrarily high private bases supplies the
same frame at any target allocator, even for aliased operands. -/
noncomputable def dynamic_of_canonical
    (canonical : ∀ b, 12 < b → KDerivation (frame b 0 1 7 8).encode)
    (b x y s t : Nat) (hx : x < b+2) (hy : y < b+2) (hs : s < b+2) (ht : t < b+2) :
    KDerivation (frame b x y s t).encode := by
  let tmp := max (max (max (max 8 x) y) s) t + 1
  let high := max b (tmp+4) + 20
  have ht' : max (max (max (max 8 x) y) s) t < tmp := by dsimp [tmp]; omega
  have hh : tmp+3 < high := by dsimp [high]; omega
  have hc : 12 < high := by dsimp [high]; omega
  have hp := instantiate_frame high x y s t tmp ht' hh (canonical high hc)
  have he := (frame_base_alpha high b x y s t (by omega) (by omega) (by omega) (by omega) hx hy hs ht).forward
  exact .mp hp he

end PASoundness.PAtoCompactQuotSuccCancellationDynamicInstantiate

#print axioms PASoundness.PAtoCompactQuotSuccCancellationDynamicInstantiate.instantiate_frame
#print axioms PASoundness.PAtoCompactQuotSuccCancellationDynamicInstantiate.frame_base_alpha
#print axioms PASoundness.PAtoCompactQuotSuccCancellationDynamicInstantiate.dynamic_of_canonical
