import PASoundness.PAtoCompactProductMatchDomainCongruence
import PASoundness.PAtoCompactMulTermTransportWitness
import PASoundness.PAtoCompactVacuousEqualityAlignment
import PASoundness.PAtoCompactDynamicSymmetryInstantiate

/-! Capture-safe reassignment of one free name in the product congruence
frame. The operation permits the new name to coincide with other operands. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchInstantiateName

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactMulTermTransportWitness PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactTemplateBlockShift

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def frame (b x y z u v w : Nat) : Formula :=
  .imp (mulAt b x y z) (.imp (mulAt b u v w)
    (.imp (equivAt b x u) (.imp (equivAt b y v)
      (.imp (domainAt b z) (equivAt b z w)))))

theorem frame_private (b x y z u v w a : Nat) (h : a ∈ (frame b x y z u v w).binders) :
    b + 2 ≤ a ∧ a < b + 64 := by
  simp only [frame, Formula.binders, Finset.mem_union] at h
  rcases h with h | h | h | h | h | h
  · exact mulAt_private b x y z a h
  · exact mulAt_private b u v w a h
  · exact equivAt_private b x u a h
  · exact equivAt_private b y v a h
  · exact domainAt_private b z a h
  · exact equivAt_private b z w a h

theorem frame_below_not_binder (b x y z u v w a : Nat) (ha : a < b + 2) :
    a ∉ (frame b x y z u v w).binders := by
  intro h
  have hp := frame_private b x y z u v w a h
  omega

theorem domain_replace (b q r s : Nat) (hr : r < b) :
    replace r s (domainAt b q) = domainAt b (rename r s q) := by
  have hn : r ∉ (domainAt b q).binders := by
    intro h
    have hp := domainAt_private b q r h
    omega
  have hs : ∀ i < 64, rename r s (b + i) = b + i := by
    intro i hi
    have hne : b + i ≠ r := by omega
    simp [rename, hne]
  rw [← map_eq_replace r s _ hn]
  exact domainAt_shift _ b b q hs

theorem frame_replace (b x y z u v w r s : Nat) (hr : r < b) :
    replace r s (frame b x y z u v w) =
      frame b (rename r s x) (rename r s y) (rename r s z)
        (rename r s u) (rename r s v) (rename r s w) := by
  change Formula.imp (replace r s (mulAt b x y z))
    (.imp (replace r s (mulAt b u v w)) (.imp (replace r s (equivAt b x u))
      (.imp (replace r s (equivAt b y v)) (.imp (replace r s (domainAt b z))
        (replace r s (equivAt b z w)))))) = _
  rw [replace_mulAt b x y z r s (by omega), replace_mulAt b u v w r s (by omega),
    equivAt_replace b x u r s (by omega), equivAt_replace b y v r s (by omega),
    domain_replace b z r s hr, equivAt_replace b z w r s (by omega)]
  rfl

/-- One admissible free-name reassignment is justified by actual K proof
data; labels may collapse, and no value inequality is assumed. -/
def instantiate_name (b x y z u v w r s : Nat) (hr : r < b) (hs : s < b + 2)
    (h : KDerivation (frame b x y z u v w).encode) :
    KDerivation (frame b (rename r s x) (rename r s y) (rename r s z)
      (rename r s u) (rename r s v) (rename r s w)).encode := by
  have h' := replace_derivation r s (frame b x y z u v w)
    (frame_below_not_binder b x y z u v w r (by omega))
    (frame_below_not_binder b x y z u v w s hs) h
  rw [frame_replace b x y z u v w r s hr] at h'
  exact h'

theorem instantiate_name_certificate (b x y z u v w r s : Nat) (hr : r < b) (hs : s < b + 2)
    (h : KDerivation (frame b x y z u v w).encode) :
    theoremCode (certificate (instantiate_name b x y z u v w r s hr hs h)) =
      (frame b (rename r s x) (rename r s y) (rename r s z)
        (rename r s u) (rename r s v) (rename r s w)).encode := certificate_correct _

end PASoundness.PAtoCompactProductMatchInstantiateName

#print axioms PASoundness.PAtoCompactProductMatchInstantiateName.instantiate_name
#print axioms PASoundness.PAtoCompactProductMatchInstantiateName.instantiate_name_certificate
