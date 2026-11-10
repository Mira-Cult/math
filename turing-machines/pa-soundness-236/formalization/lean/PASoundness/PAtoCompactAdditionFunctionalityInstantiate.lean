import PASoundness.PAtoCompactAdditionDomainFunctionality
import PASoundness.PAtoCompactProductMatchInstantiateName

/-! Capture-safe free-name reassignment for the fixed-base addition
functionality frame; assigned labels may coincide. -/
namespace PASoundness.PAtoCompactAdditionFunctionalityInstantiate

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactAddTermBody
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactProductMatchInstantiateName

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle
attribute [local irreducible] domainAt addAt equivAt

def frame (b x y z w : Nat) : Formula := .imp
  (namedBoth (domainAt b x) (namedBoth (domainAt b y) (namedBoth (domainAt b z)
    (namedBoth (domainAt b w) (namedBoth (addAt b x y z) (addAt b x y w))))))
  (equivAt b z w)

theorem frame_private (b x y z w a : Nat) (h : a ∈ (frame b x y z w).binders) :
    b + 2 ≤ a ∧ a < b + 64 := by
  simp only [frame, namedBoth, Formula.not, Formula.binders, Finset.empty_union,
    Finset.union_empty, Finset.mem_union] at h
  rcases h with h | he
  · rcases h with h | h | h | h | h | h
    · exact domainAt_private b x a h
    · exact domainAt_private b y a h
    · exact domainAt_private b z a h
    · exact domainAt_private b w a h
    · exact addAt_private b x y z a h
    · exact addAt_private b x y w a h
  · exact equivAt_private b z w a he

theorem frame_not_binder (b x y z w a : Nat) (h : a < b + 2) :
    a ∉ (frame b x y z w).binders := by
  intro ha
  have hp := frame_private b x y z w a ha
  omega

theorem frame_replace (b x y z w r s : Nat) (hr : r < b) :
    replace r s (frame b x y z w) = frame b (rename r s x) (rename r s y)
      (rename r s z) (rename r s w) := by
  change Formula.imp (namedBoth (replace r s (domainAt b x))
    (namedBoth (replace r s (domainAt b y)) (namedBoth (replace r s (domainAt b z))
      (namedBoth (replace r s (domainAt b w)) (namedBoth (replace r s (addAt b x y z))
        (replace r s (addAt b x y w))))))) (replace r s (equivAt b z w)) = _
  rw [domain_replace b x r s hr, domain_replace b y r s hr,
    domain_replace b z r s hr, domain_replace b w r s hr,
    replace_addAt b x y z r s (by omega), replace_addAt b x y w r s (by omega),
    equivAt_replace b z w r s (by omega)]
  rfl

/-- Reassign one source name below the private block; the target may alias
another free name. -/
def instantiate_name (b x y z w r s : Nat) (hr : r < b) (hs : s < b + 2)
    (h : KDerivation (frame b x y z w).encode) :
    KDerivation (frame b (rename r s x) (rename r s y) (rename r s z) (rename r s w)).encode := by
  have h' := replace_derivation r s (frame b x y z w)
    (frame_not_binder b x y z w r (by omega)) (frame_not_binder b x y z w s hs) h
  rw [frame_replace b x y z w r s hr] at h'
  exact h'

end PASoundness.PAtoCompactAdditionFunctionalityInstantiate

#print axioms PASoundness.PAtoCompactAdditionFunctionalityInstantiate.frame
#print axioms PASoundness.PAtoCompactAdditionFunctionalityInstantiate.frame_private
#print axioms PASoundness.PAtoCompactAdditionFunctionalityInstantiate.frame_not_binder
#print axioms PASoundness.PAtoCompactAdditionFunctionalityInstantiate.frame_replace
#print axioms PASoundness.PAtoCompactAdditionFunctionalityInstantiate.instantiate_name
