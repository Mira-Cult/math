import PASoundness.PAtoCompactAdditionFixedOperandCongruence
import PASoundness.PAtoCompactProductMatchInstantiateName

/-! Capture-safe free-name reassignment for the fixed-base addition
congruence frame. Both oriented operand equivalences are explicit. -/
namespace PASoundness.PAtoCompactAdditionCongruenceInstantiate

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactAddTermBody
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactProductMatchInstantiateName

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle
attribute [local irreducible] domainAt addAt equivAt

def frame (b x y z u v w : Nat) : Formula := .imp
  (namedBoth (domainAt b u) (namedBoth (domainAt b v) (namedBoth (equivAt b u x)
    (namedBoth (equivAt b v y) (namedBoth (domainAt b z) (namedBoth (domainAt b w)
      (namedBoth (addAt b x y z) (addAt b u v w)))))))) (equivAt b z w)

theorem frame_private (b x y z u v w a : Nat) (h : a ∈ (frame b x y z u v w).binders) :
    b + 2 ≤ a ∧ a < b + 64 := by
  simp only [frame, namedBoth, Formula.not, Formula.binders, Finset.empty_union,
    Finset.union_empty, Finset.mem_union] at h
  rcases h with h | he
  · rcases h with h | h | h | h | h | h | h | h
    · exact domainAt_private b u a h
    · exact domainAt_private b v a h
    · exact equivAt_private b u x a h
    · exact equivAt_private b v y a h
    · exact domainAt_private b z a h
    · exact domainAt_private b w a h
    · exact addAt_private b x y z a h
    · exact addAt_private b u v w a h
  · exact equivAt_private b z w a he

theorem frame_not_binder (b x y z u v w a : Nat) (h : a < b + 2) :
    a ∉ (frame b x y z u v w).binders := by
  intro ha
  have hp := frame_private b x y z u v w a ha
  omega

theorem frame_replace (b x y z u v w r s : Nat) (hr : r < b) :
    replace r s (frame b x y z u v w) = frame b (rename r s x) (rename r s y)
      (rename r s z) (rename r s u) (rename r s v) (rename r s w) := by
  change Formula.imp (namedBoth (replace r s (domainAt b u))
    (namedBoth (replace r s (domainAt b v)) (namedBoth (replace r s (equivAt b u x))
      (namedBoth (replace r s (equivAt b v y)) (namedBoth (replace r s (domainAt b z))
        (namedBoth (replace r s (domainAt b w)) (namedBoth (replace r s (addAt b x y z))
          (replace r s (addAt b u v w))))))))) (replace r s (equivAt b z w)) = _
  rw [domain_replace b u r s hr, domain_replace b v r s hr,
    equivAt_replace b u x r s (by omega), equivAt_replace b v y r s (by omega),
    domain_replace b z r s hr, domain_replace b w r s hr,
    replace_addAt b x y z r s (by omega), replace_addAt b u v w r s (by omega),
    equivAt_replace b z w r s (by omega)]
  rfl

/-- A replacement target may alias another free operand or result name. -/
def instantiate_name (b x y z u v w r s : Nat) (hr : r < b) (hs : s < b + 2)
    (h : KDerivation (frame b x y z u v w).encode) :
    KDerivation (frame b (rename r s x) (rename r s y) (rename r s z)
      (rename r s u) (rename r s v) (rename r s w)).encode := by
  have h' := replace_derivation r s (frame b x y z u v w)
    (frame_not_binder b x y z u v w r (by omega)) (frame_not_binder b x y z u v w s hs) h
  rw [frame_replace b x y z u v w r s hr] at h'
  exact h'

end PASoundness.PAtoCompactAdditionCongruenceInstantiate

#print axioms PASoundness.PAtoCompactAdditionCongruenceInstantiate.frame
#print axioms PASoundness.PAtoCompactAdditionCongruenceInstantiate.frame_private
#print axioms PASoundness.PAtoCompactAdditionCongruenceInstantiate.frame_not_binder
#print axioms PASoundness.PAtoCompactAdditionCongruenceInstantiate.frame_replace
#print axioms PASoundness.PAtoCompactAdditionCongruenceInstantiate.instantiate_name
