import PASoundness.PAtoCompactFreeNames
import PASoundness.PAtoCompactSafeStepsInitial
import PASoundness.PAtoCompactEquivNoShadow
import PASoundness.PAtoCompactEquivStepsSyntax

/-! Freshness ingredients for moving the private bound names of `equivAt`.
The two free operand labels may coincide. -/
namespace PASoundness.PAtoCompactEquivMultiAlpha

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactSafeStepsInitial PASoundness.PAtoCompactMultiAlpha
open PASoundness.PAtoCompactEquivNoShadow PASoundness.PAtoCompactEquivStepsSyntax

/-- Every name in the template instance is an operand or lies in its
private allocator block. -/
theorem equivAt_name_bound (b x y z : Nat) (h : z ∈ (equivAt b x y).names) :
    z = x ∨ z = y ∨ (b + 2 ≤ z ∧ z < b + 40) := by
  unfold equivAt at h
  rw [mapNames_names] at h
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp h
  have hkbound := templates_names_bounded.2.1 hk
  simp only [Finset.mem_range] at hkbound
  by_cases hk0 : k = 0
  · left
    simpa [twoMap, hk0] using he.symm
  · by_cases hk1 : k = 1
    · right; left
      simpa [twoMap, hk0, hk1] using he.symm
    · right; right
      simp [twoMap, hk0, hk1] at he
      omega

theorem equivAt_old_not_free (b x y k : Nat) (hx : x < b + 2) (hy : y < b + 2) :
    b + 2 + k ∉ (equivAt b x y).free := by
  intro h
  have hh := equivAt_free b x y h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with h | h <;> omega

theorem equivAt_new_not_names (b c x y k : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hdis : b + 39 < c + 2) :
    c + 2 + k ∉ (equivAt b x y).names := by
  intro h
  rcases equivAt_name_bound b x y _ h with h | h | h <;> omega

/-- All nine old-to-new binder moves satisfy the initial conditions for
the finite K alpha construction. -/
theorem equiv_initial_safe (b c x y : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hdis : b + 39 < c + 2) :
    InitialSafe (equivSteps b c) (equivAt b x y) := by
  refine ⟨?_, ?_, equivAt_allNoShadow b x y⟩
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact ⟨by simp only; omega, equivAt_old_not_free b x y k hx hy,
      equivAt_new_not_names b c x y k hx hy hdis⟩
  · simp only [equivSteps, offsets, List.map_cons, List.map_nil,
      List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
      not_false_eq_true, not_or, and_true]
    omega

/-- Nine concrete K alpha moves give the exact equivalence instance at the
new disjoint base. The two operands may coincide. -/
def equivAt_disjoint_alpha (b c x y : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hdis : b + 39 < c + 2) :
    ProofEquiv (equivAt b x y) (equivAt c x y) := by
  have hs := initial_safe_steps (equivSteps b c) (equivAt b x y)
    (equiv_initial_safe b c x y hx hy hdis)
  have h := multiAlpha (equivSteps b c) (equivAt b x y) hs
  rw [renameSteps_equivAt b c x y hdis hx hy] at h
  exact h

/-- Transport the quotient-equivalence template between arbitrary private
blocks. A third fresh block handles overlap, and input labels may coincide. -/
def equivAt_base_alpha (b c x y : Nat)
    (hxb : x < b + 2) (hyb : y < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) :
    ProofEquiv (equivAt b x y) (equivAt c x y) := by
  let d := max b c + 100
  have hbd : b + 39 < d + 2 := by dsimp [d]; omega
  have hcd : c + 39 < d + 2 := by dsimp [d]; omega
  exact (equivAt_disjoint_alpha b d x y hxb hyb hbd).trans
    (equivAt_disjoint_alpha c d x y hxc hyc hcd).symm

theorem equivAt_base_forward_certificate (b c x y : Nat)
    (hxb : x < b + 2) (hyb : y < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) :
    theoremCode (certificate (equivAt_base_alpha b c x y hxb hyb hxc hyc).forward) =
      PASoundness.CompactProof.imp (equivAt b x y).encode (equivAt c x y).encode :=
  PASoundness.CompactProof.certificate_correct _

theorem equivAt_base_backward_certificate (b c x y : Nat)
    (hxb : x < b + 2) (hyb : y < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) :
    theoremCode (certificate (equivAt_base_alpha b c x y hxb hyb hxc hyc).backward) =
      PASoundness.CompactProof.imp (equivAt c x y).encode (equivAt b x y).encode :=
  PASoundness.CompactProof.certificate_correct _

end PASoundness.PAtoCompactEquivMultiAlpha

#print axioms PASoundness.PAtoCompactEquivMultiAlpha.equivAt_name_bound
#print axioms PASoundness.PAtoCompactEquivMultiAlpha.equivAt_old_not_free
#print axioms PASoundness.PAtoCompactEquivMultiAlpha.equivAt_new_not_names
#print axioms PASoundness.PAtoCompactEquivMultiAlpha.equiv_initial_safe
#print axioms PASoundness.PAtoCompactEquivMultiAlpha.equivAt_disjoint_alpha
#print axioms PASoundness.PAtoCompactEquivMultiAlpha.equivAt_base_alpha
#print axioms PASoundness.PAtoCompactEquivMultiAlpha.equivAt_base_forward_certificate
#print axioms PASoundness.PAtoCompactEquivMultiAlpha.equivAt_base_backward_certificate
