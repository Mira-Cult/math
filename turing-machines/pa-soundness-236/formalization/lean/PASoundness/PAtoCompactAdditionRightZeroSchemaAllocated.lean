import PASoundness.PAtoCompactAdditionRightZeroSchema
import PASoundness.PAtoCompactAdditionZeroAllocated
import PASoundness.PAtoCompactZeroGraphOutputTransport
import PASoundness.PAtoCompactAddBaseMultiAlpha

/-! K transport of the right-zero addition equivalence to arbitrary allocated
operand names. Fresh temporary names prevent collisions even when operands alias. -/
namespace PASoundness.PAtoCompactAdditionRightZeroSchemaAllocated

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroBaseTransport
open PASoundness.PAtoCompactTemplateBlockShift PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactAddBaseMultiAlpha

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def frame (reverse : Bool) (b a z q : Nat) : Formula :=
  if reverse then .imp (zeroAt b z) (.imp (equivAt b a q) (addAt b a z q))
  else .imp (zeroAt b z) (.imp (addAt b a z q) (equivAt b a q))

theorem frame_not_binder (reverse : Bool) (b a z q k : Nat) (hk : k < b) :
    k ∉ (frame reverse b a z q).binders := by
  have hz : k ∉ (zeroAt b z).binders := by
    intro h
    have hh := zeroAt_private b z k h
    omega
  have ha : k ∉ (addAt b a z q).binders := by
    intro h
    have hh := addAt_private b a z q k h
    omega
  have he : k ∉ (equivAt b a q).binders := by
    intro h
    have hh := equivAt_private b a q k h
    omega
  cases reverse <;> simp [frame, Formula.binders, hz, ha, he]

theorem frame_replace (reverse : Bool) (b a z q k w : Nat) (hk : k < b) :
    replace k w (frame reverse b a z q) =
      frame reverse b (rename k w a) (rename k w z) (rename k w q) := by
  have hf : ∀ i < 64, rename k w (b+i) = b+i := by
    intro i hi
    simp [rename, show b+i ≠ k by omega]
  have hz : replace k w (zeroAt b z) = zeroAt b (rename k w z) := by
    rw [← map_eq_replace k w _ (by intro h; have := zeroAt_private b z k h; omega)]
    exact zeroAt_shift (rename k w) b b z hf
  have ha : replace k w (addAt b a z q) =
      addAt b (rename k w a) (rename k w z) (rename k w q) := by
    rw [← map_eq_replace k w _ (by intro h; have := addAt_private b a z q k h; omega)]
    exact addAt_shift (rename k w) b b a z q hf
  have he : replace k w (equivAt b a q) = equivAt b (rename k w a) (rename k w q) := by
    rw [← map_eq_replace k w _ (by intro h; have := equivAt_private b a q k h; omega)]
    exact equivAt_shift (rename k w) b b a q hf
  cases reverse <;> simp only [frame, Bool.false_eq_true, ↓reduceIte, replace, hz, ha, he]

/-- Specialize a fixed-operand K derivation at arbitrary operands below b.
The two high temporary names are disjoint from all operands and 30,31,32. -/
def specialize_high (reverse : Bool) (b a z q : Nat)
    (hb : 34 < b) (ha : a < b) (hz : z < b) (hq : q < b)
    (space : max a (max z q) + 35 < b)
    (fixed : KDerivation (frame reverse b 30 31 32).encode) :
    KDerivation (frame reverse b a z q).encode := by
  let p := max a (max z q) + 33
  let r := p + 1
  have hp : p < b := by dsimp [p] at *; omega
  have hr : r < b := by dsimp [r,p] at *; omega
  have h0 := replace_derivation 30 p (frame reverse b 30 31 32)
    (frame_not_binder reverse b 30 31 32 30 (by omega))
    (frame_not_binder reverse b 30 31 32 p hp) fixed
  have h0s : replace 30 p (frame reverse b 30 31 32) = frame reverse b p 31 32 := by
    simpa [rename] using frame_replace reverse b 30 31 32 30 p (by omega)
  rw [h0s] at h0
  have h1 := replace_derivation 31 r (frame reverse b p 31 32)
    (frame_not_binder reverse b p 31 32 31 (by omega))
    (frame_not_binder reverse b p 31 32 r hr) h0
  have h1s : replace 31 r (frame reverse b p 31 32) = frame reverse b p r 32 := by
    have hp31 : p ≠ 31 := by dsimp [p]; omega
    simpa [rename, hp31] using frame_replace reverse b p 31 32 31 r (by omega)
  rw [h1s] at h1
  have h2 := replace_derivation 32 q (frame reverse b p r 32)
    (frame_not_binder reverse b p r 32 32 (by omega))
    (frame_not_binder reverse b p r 32 q hq) h1
  have h2s : replace 32 q (frame reverse b p r 32) = frame reverse b p r q := by
    have hp32 : p ≠ 32 := by dsimp [p]; omega
    have hr32 : r ≠ 32 := by dsimp [r,p]; omega
    simpa [rename, hp32, hr32] using frame_replace reverse b p r 32 32 q (by omega)
  rw [h2s] at h2
  have h3 := replace_derivation p a (frame reverse b p r q)
    (frame_not_binder reverse b p r q p hp)
    (frame_not_binder reverse b p r q a ha) h2
  have h3s : replace p a (frame reverse b p r q) = frame reverse b a r q := by
    have hrp : r ≠ p := by dsimp [r]; omega
    have hqp : q ≠ p := by dsimp [p]; omega
    simpa [rename, hrp, hqp] using frame_replace reverse b p r q p a hp
  rw [h3s] at h3
  have h4 := replace_derivation r z (frame reverse b a r q)
    (frame_not_binder reverse b a r q r hr)
    (frame_not_binder reverse b a r q z hz) h3
  have h4s : replace r z (frame reverse b a r q) = frame reverse b a z q := by
    have har : a ≠ r := by dsimp [r,p]; omega
    have hqr : q ≠ r := by dsimp [r,p]; omega
    simpa [rename, har, hqr] using frame_replace reverse b a r q r z hr
  simpa only [h4s] using h4

/-- Change all private allocation blocks in a fixed-direction schema. -/
def rebase_frame (reverse : Bool) (b c a z q : Nat)
    (hab : a < b+2) (hzb : z < b+2) (hqb : q < b+2)
    (hac : a < c+2) (hzc : z < c+2) (hqc : q < c+2)
    (high : KDerivation (frame reverse c a z q).encode) :
    KDerivation (frame reverse b a z q).encode := by
  have hz := zeroAt_base_forward b c z (by omega) (by omega)
  have add := addAt_base_alpha b c a z q hab hzb hqb hac hzc hqc
  have eq := equivAt_base_alpha b c a q hab hqb hac hqc
  cases reverse with
  | false =>
      change KDerivation (imp (zeroAt b z).encode
        (imp (addAt b a z q).encode (equivAt b a q).encode))
      apply Context.closeEmpty
      apply Context.deduction
      apply Context.deduction
      let Γ := [(addAt b a z q).encode, (zeroAt b z).encode]
      have hA : Context Γ (addAt b a z q).encode := Context.head _ _
      have hZ : Context Γ (zeroAt b z).encode := .hypothesis (by simp [Γ])
      have hz' := Context.mp hZ (.closed hz)
      have ha' := Context.mp hA (.closed add.forward)
      have he' : Context Γ (equivAt c a q).encode := .mp ha' (.mp hz' (.closed high))
      exact .mp he' (.closed eq.backward)
  | true =>
      change KDerivation (imp (zeroAt b z).encode
        (imp (equivAt b a q).encode (addAt b a z q).encode))
      apply Context.closeEmpty
      apply Context.deduction
      apply Context.deduction
      let Γ := [(equivAt b a q).encode, (zeroAt b z).encode]
      have hE : Context Γ (equivAt b a q).encode := Context.head _ _
      have hZ : Context Γ (zeroAt b z).encode := .hypothesis (by simp [Γ])
      have hz' := Context.mp hZ (.closed hz)
      have he' := Context.mp hE (.closed eq.forward)
      have ha' : Context Γ (addAt c a z q).encode := .mp he' (.mp hz' (.closed high))
      exact .mp ha' (.closed add.backward)

/-- Arbitrary-name and arbitrary-allocator schema, from its high fixed-name
instance. The required K proof input is not assumed to be constructed here. -/
def schema_of_fixed (reverse : Bool) (b a z q : Nat)
    (ha : a < b+2) (hz : z < b+2) (hq : q < b+2)
    (fixed : ∀ c, 40 ≤ c → KDerivation (frame reverse c 30 31 32).encode) :
    KDerivation (frame reverse b a z q).encode := by
  let c := max b (max a (max z q)) + 100
  have hc : 40 ≤ c := by dsimp [c]; omega
  have hac : a < c := by dsimp [c]; omega
  have hzc : z < c := by dsimp [c]; omega
  have hqc : q < c := by dsimp [c]; omega
  have hspace : max a (max z q) + 35 < c := by dsimp [c]; omega
  have high := specialize_high reverse c a z q (by omega) hac hzc hqc hspace (fixed c hc)
  exact rebase_frame reverse b c a z q ha hz hq (by omega) (by omega) (by omega) high

end PASoundness.PAtoCompactAdditionRightZeroSchemaAllocated

#print axioms PASoundness.PAtoCompactAdditionRightZeroSchemaAllocated.specialize_high
#print axioms PASoundness.PAtoCompactAdditionRightZeroSchemaAllocated.rebase_frame
#print axioms PASoundness.PAtoCompactAdditionRightZeroSchemaAllocated.schema_of_fixed
