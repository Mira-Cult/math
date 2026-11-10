import PASoundness.PAtoCompactMulBaseInventory
import PASoundness.PAtoCompactMulBaseSyntax
import PASoundness.PAtoCompactSafeStepsInitial
import PASoundness.PAtoCompactFreeNames

/-! K alpha transport of the multiplication template between private
allocator blocks, with explicit operand-label freshness. -/
namespace PASoundness.PAtoCompactMulBaseMultiAlpha

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactMultiAlpha
open PASoundness.PAtoCompactSafeStepsInitial PASoundness.PAtoCompactMulBaseInventory
open PASoundness.PAtoCompactMulBaseSyntax

theorem mulAt_name_bound (b x y z w : Nat) (h : w ∈ (mulAt b x y z).names) :
    w = x ∨ w = y ∨ w = z ∨ (b + 2 ≤ w ∧ w < b + 40) := by
  unfold mulAt at h
  rw [mapNames_names] at h
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp h
  have hkbound := templates_names_bounded.2.2.2.2.2 hk
  simp only [Finset.mem_range] at hkbound
  by_cases hk0 : k = 0
  · left; simpa [threeMap, hk0] using he.symm
  · by_cases hk1 : k = 1
    · right; left; simpa [threeMap, hk0, hk1] using he.symm
    · by_cases hk2 : k = 2
      · right; right; left; simpa [threeMap, hk0, hk1, hk2] using he.symm
      · right; right; right
        simp [threeMap, hk0, hk1, hk2] at he
        omega

theorem mulAt_old_not_free (b x y z k : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hz : z < b + 2) :
    b + 2 + k ∉ (mulAt b x y z).free := by
  intro h
  have hh := mulAt_free b x y z h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with h | h | h <;> omega

theorem mulAt_new_not_names (b c x y z k : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hz : z < b + 2)
    (hdis : b + 39 < c + 2) : c + 2 + k ∉ (mulAt b x y z).names := by
  intro h
  rcases mulAt_name_bound b x y z _ h with h | h | h | h <;> omega

theorem mul_initial_safe (b c x y z : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hz : z < b + 2)
    (hdis : b + 39 < c + 2) : InitialSafe (mulSteps b c) (mulAt b x y z) := by
  refine ⟨?_, ?_, mulAt_allNoShadow b x y z⟩
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact ⟨by simp only; omega, mulAt_old_not_free b x y z k hx hy hz,
      mulAt_new_not_names b c x y z k hx hy hz hdis⟩
  · have hn : mulOffsets.Nodup := by decide
    have hi : Function.Injective (fun k : Nat => c + 2 + k) := by
      intro i j he
      change c + 2 + i = c + 2 + j at he
      omega
    have hm := List.Nodup.map hi hn
    simpa [mulSteps, List.map_map, Function.comp_def] using hm

/-- Move every multiplication-template binder across disjoint blocks, with
no requirement that the three operand names differ. -/
def mulAt_disjoint_alpha (b c x y z : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hz : z < b + 2)
    (hdis : b + 39 < c + 2) : ProofEquiv (mulAt b x y z) (mulAt c x y z) := by
  have hs := initial_safe_steps (mulSteps b c) (mulAt b x y z)
    (mul_initial_safe b c x y z hx hy hz hdis)
  have h := multiAlpha (mulSteps b c) (mulAt b x y z) hs
  rw [renameSteps_mulAt b c x y z hdis hx hy hz] at h
  exact h

/-- A third block avoids overlapping source and target allocations. -/
def mulAt_base_alpha (b c x y z : Nat)
    (hxb : x < b + 2) (hyb : y < b + 2) (hzb : z < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) (hzc : z < c + 2) :
    ProofEquiv (mulAt b x y z) (mulAt c x y z) := by
  let d := max b c + 100
  have hbd : b + 39 < d + 2 := by dsimp [d]; omega
  have hcd : c + 39 < d + 2 := by dsimp [d]; omega
  exact (mulAt_disjoint_alpha b d x y z hxb hyb hzb hbd).trans
    (mulAt_disjoint_alpha c d x y z hxc hyc hzc hcd).symm

theorem mulAt_base_forward_certificate (b c x y z : Nat)
    (hxb : x < b + 2) (hyb : y < b + 2) (hzb : z < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) (hzc : z < c + 2) :
    theoremCode (certificate (mulAt_base_alpha b c x y z hxb hyb hzb hxc hyc hzc).forward) =
      imp (mulAt b x y z).encode (mulAt c x y z).encode := certificate_correct _

theorem mulAt_base_backward_certificate (b c x y z : Nat)
    (hxb : x < b + 2) (hyb : y < b + 2) (hzb : z < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) (hzc : z < c + 2) :
    theoremCode (certificate (mulAt_base_alpha b c x y z hxb hyb hzb hxc hyc hzc).backward) =
      imp (mulAt c x y z).encode (mulAt b x y z).encode := certificate_correct _

end PASoundness.PAtoCompactMulBaseMultiAlpha

#print axioms PASoundness.PAtoCompactMulBaseMultiAlpha.mulAt_name_bound
#print axioms PASoundness.PAtoCompactMulBaseMultiAlpha.mulAt_old_not_free
#print axioms PASoundness.PAtoCompactMulBaseMultiAlpha.mulAt_new_not_names
#print axioms PASoundness.PAtoCompactMulBaseMultiAlpha.mul_initial_safe
#print axioms PASoundness.PAtoCompactMulBaseMultiAlpha.mulAt_disjoint_alpha
#print axioms PASoundness.PAtoCompactMulBaseMultiAlpha.mulAt_base_alpha
#print axioms PASoundness.PAtoCompactMulBaseMultiAlpha.mulAt_base_forward_certificate
#print axioms PASoundness.PAtoCompactMulBaseMultiAlpha.mulAt_base_backward_certificate
