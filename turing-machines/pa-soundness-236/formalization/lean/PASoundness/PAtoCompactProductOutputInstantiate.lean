import PASoundness.PAtoCompactProductOutputFixedBase
import PASoundness.PAtoCompactProductMatchInstantiateName

/-! Capture-safe reassignment of one free name in the product-output frame.
The destination can coincide with any other operand label. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputInstantiate

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactMulTermTransportWitness
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactProductMatchInstantiateName
open PASoundness.PAtoCompactProductOutputFixedBase

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

theorem frame_private (b x y p q a : Nat) (h : a ∈ (PAtoCompactProductOutputFixedBase.frame b x y p q).binders) :
    b + 2 ≤ a ∧ a < b + 64 := by
  simp only [PAtoCompactProductOutputFixedBase.frame, Formula.binders, Finset.mem_union] at h
  rcases h with h | h | h | h
  · exact mulAt_private b x y p a h
  · exact equivAt_private b p q a h
  · exact domainAt_private b p a h
  · exact mulAt_private b x y q a h

theorem frame_below_not_binder (b x y p q a : Nat) (ha : a < b + 2) :
    a ∉ (PAtoCompactProductOutputFixedBase.frame b x y p q).binders := by
  intro h
  have hp := frame_private b x y p q a h
  omega

theorem frame_replace (b x y p q r s : Nat) (hr : r < b) :
    replace r s (PAtoCompactProductOutputFixedBase.frame b x y p q) =
      PAtoCompactProductOutputFixedBase.frame b (rename r s x) (rename r s y) (rename r s p) (rename r s q) := by
  change Formula.imp (replace r s (mulAt b x y p))
    (.imp (replace r s (equivAt b p q)) (.imp (replace r s (domainAt b p))
      (replace r s (mulAt b x y q)))) = _
  rw [replace_mulAt b x y p r s (by omega), equivAt_replace b p q r s (by omega),
    domain_replace b p r s hr, replace_mulAt b x y q r s (by omega)]
  rfl

def instantiate_name (b x y p q r s : Nat) (hr : r < b) (hs : s < b + 2)
    (h : KDerivation (PAtoCompactProductOutputFixedBase.frame b x y p q).encode) :
    KDerivation (PAtoCompactProductOutputFixedBase.frame b (rename r s x) (rename r s y)
      (rename r s p) (rename r s q)).encode := by
  have h' := replace_derivation r s (PAtoCompactProductOutputFixedBase.frame b x y p q)
    (frame_below_not_binder b x y p q r (by omega))
    (frame_below_not_binder b x y p q s hs) h
  rw [frame_replace b x y p q r s hr] at h'
  exact h'

theorem instantiate_name_certificate (b x y p q r s : Nat) (hr : r < b) (hs : s < b + 2)
    (h : KDerivation (PAtoCompactProductOutputFixedBase.frame b x y p q).encode) :
    theoremCode (certificate (instantiate_name b x y p q r s hr hs h)) =
      (PAtoCompactProductOutputFixedBase.frame b (rename r s x) (rename r s y)
        (rename r s p) (rename r s q)).encode := certificate_correct _

end PASoundness.PAtoCompactProductOutputInstantiate

#print axioms PASoundness.PAtoCompactProductOutputInstantiate.instantiate_name
#print axioms PASoundness.PAtoCompactProductOutputInstantiate.instantiate_name_certificate
