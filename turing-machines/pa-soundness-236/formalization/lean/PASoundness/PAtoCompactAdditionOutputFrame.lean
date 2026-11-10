import PASoundness.PAtoCompactAdditionFunctionalityInstantiate

/-! Capture-safe free-label reassignment for the four-domain addition-output
transport frame. This module does not prove the frame; it transports supplied
finite K proof data. Labels and denoted objects may coincide. -/
namespace PASoundness.PAtoCompactAdditionOutputFrame
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactAddTermBody PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactProductMatchInstantiateName
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle
attribute [local irreducible] domainAt addAt equivAt

/-- Exact relation-level frame. All four domain assumptions are explicit. -/
def frame (b x y q r : Nat) : Formula := .imp (addAt b x y q)
  (.imp (domainAt b q) (.imp (domainAt b r) (.imp (domainAt b y)
    (.imp (domainAt b x) (.imp (equivAt b q r) (addAt b x y r))))))

/-- Every binder in this frame belongs to the allocator's private range. -/
theorem frame_private (b x y q r a : Nat) (h : a ∈ (frame b x y q r).binders) :
    b + 2 ≤ a ∧ a < b + 64 := by
  simp only [frame,Formula.binders,Finset.mem_union] at h
  rcases h with h | hrest
  · exact addAt_private b x y q a h
  · rcases hrest with h | hrest
    · exact domainAt_private b q a h
    · rcases hrest with h | hrest
      · exact domainAt_private b r a h
      · rcases hrest with h | hrest
        · exact domainAt_private b y a h
        · rcases hrest with h | hrest
          · exact domainAt_private b x a h
          · rcases hrest with he | hout
            · exact equivAt_private b q r a he
            · exact addAt_private b x y r a hout

theorem frame_not_binder (b x y q r a : Nat) (h : a < b + 2) :
    a ∉ (frame b x y q r).binders := by
  intro ha
  have hp := frame_private b x y q r a ha
  omega

/-- Replacing a source name below the private range changes only the frame's
four displayed labels, including any repeated occurrences. -/
theorem frame_replace (b x y q r a c : Nat) (ha : a < b) :
    replace a c (frame b x y q r) = frame b (rename a c x) (rename a c y)
      (rename a c q) (rename a c r) := by
  change Formula.imp (replace a c (addAt b x y q))
    (.imp (replace a c (domainAt b q)) (.imp (replace a c (domainAt b r))
      (.imp (replace a c (domainAt b y)) (.imp (replace a c (domainAt b x))
        (.imp (replace a c (equivAt b q r)) (replace a c (addAt b x y r))))))) = _
  rw [replace_addAt b x y q a c (by omega), domain_replace b q a c ha,
    domain_replace b r a c ha, domain_replace b y a c ha, domain_replace b x a c ha,
    equivAt_replace b q r a c (by omega), replace_addAt b x y r a c (by omega)]
  rfl

/-- Reassign one free name while avoiding private binders. The destination
may alias any other displayed label. -/
def instantiate_name (b x y q r a c : Nat) (ha : a < b) (hc : c < b + 2)
    (h : KDerivation (frame b x y q r).encode) :
    KDerivation (frame b (rename a c x) (rename a c y) (rename a c q) (rename a c r)).encode := by
  have h' := replace_derivation a c (frame b x y q r)
    (frame_not_binder b x y q r a (by omega)) (frame_not_binder b x y q r c hc) h
  rw [frame_replace b x y q r a c ha] at h'
  exact h'
end PASoundness.PAtoCompactAdditionOutputFrame

#print axioms PASoundness.PAtoCompactAdditionOutputFrame.frame
#print axioms PASoundness.PAtoCompactAdditionOutputFrame.frame_private
#print axioms PASoundness.PAtoCompactAdditionOutputFrame.frame_not_binder
#print axioms PASoundness.PAtoCompactAdditionOutputFrame.frame_replace
#print axioms PASoundness.PAtoCompactAdditionOutputFrame.instantiate_name
