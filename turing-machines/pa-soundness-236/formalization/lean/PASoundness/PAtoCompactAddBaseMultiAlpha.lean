import PASoundness.PAtoCompactAddBaseInventory
import PASoundness.PAtoCompactAddBaseSyntax
import PASoundness.PAtoCompactSafeStepsInitial
import PASoundness.PAtoCompactFreeNames

/-! Finite K alpha transport of the addition template across private blocks.
The three input labels may coincide; freshness concerns labels and binders. -/
namespace PASoundness.PAtoCompactAddBaseMultiAlpha

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactMultiAlpha
open PASoundness.PAtoCompactSafeStepsInitial PASoundness.PAtoCompactAddBaseInventory
open PASoundness.PAtoCompactAddBaseSyntax

theorem addAt_name_bound (b x y z w : Nat) (h : w ∈ (addAt b x y z).names) :
    w = x ∨ w = y ∨ w = z ∨ (b + 2 ≤ w ∧ w < b + 40) := by
  unfold addAt at h
  rw [mapNames_names] at h
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp h
  have hkbound := templates_names_bounded.2.2.2.2.1 hk
  simp only [Finset.mem_range] at hkbound
  by_cases hk30 : k = 30
  · left; simpa [threeMap, hk30] using he.symm
  · by_cases hk31 : k = 31
    · right; left; simpa [threeMap, hk30, hk31] using he.symm
    · by_cases hk32 : k = 32
      · right; right; left; simpa [threeMap, hk30, hk31, hk32] using he.symm
      · right; right; right
        simp [threeMap, hk30, hk31, hk32] at he
        omega

theorem addAt_old_not_free (b x y z k : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hz : z < b + 2) :
    b + 2 + k ∉ (addAt b x y z).free := by
  intro h
  have hh := addAt_free b x y z h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with h | h | h <;> omega

theorem addAt_new_not_names (b c x y z k : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hz : z < b + 2)
    (hdis : b + 39 < c + 2) : c + 2 + k ∉ (addAt b x y z).names := by
  intro h
  rcases addAt_name_bound b x y z _ h with h | h | h | h <;> omega

theorem add_initial_safe (b c x y z : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hz : z < b + 2)
    (hdis : b + 39 < c + 2) : InitialSafe (addSteps b c) (addAt b x y z) := by
  refine ⟨?_, ?_, addAt_allNoShadow b x y z⟩
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact ⟨by simp only; omega, addAt_old_not_free b x y z k hx hy hz,
      addAt_new_not_names b c x y z k hx hy hz hdis⟩
  · have hn : addOffsets.Nodup := by decide
    have hi : Function.Injective (fun k : Nat => c + 2 + k) := by
      intro i j he
      change c + 2 + i = c + 2 + j at he
      omega
    have hm := List.Nodup.map hi hn
    simpa [addSteps, List.map_map, Function.comp_def] using hm

/-- Move the addition-template binders between disjoint blocks in K. -/
def addAt_disjoint_alpha (b c x y z : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hz : z < b + 2)
    (hdis : b + 39 < c + 2) : ProofEquiv (addAt b x y z) (addAt c x y z) := by
  have hs := initial_safe_steps (addSteps b c) (addAt b x y z)
    (add_initial_safe b c x y z hx hy hz hdis)
  have h := multiAlpha (addSteps b c) (addAt b x y z) hs
  rw [renameSteps_addAt b c x y z hdis hx hy hz] at h
  exact h

/-- A third disjoint block handles overlapping source and target blocks. -/
def addAt_base_alpha (b c x y z : Nat)
    (hxb : x < b + 2) (hyb : y < b + 2) (hzb : z < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) (hzc : z < c + 2) :
    ProofEquiv (addAt b x y z) (addAt c x y z) := by
  let d := max b c + 100
  have hbd : b + 39 < d + 2 := by dsimp [d]; omega
  have hcd : c + 39 < d + 2 := by dsimp [d]; omega
  exact (addAt_disjoint_alpha b d x y z hxb hyb hzb hbd).trans
    (addAt_disjoint_alpha c d x y z hxc hyc hzc hcd).symm

theorem addAt_base_forward_certificate (b c x y z : Nat)
    (hxb : x < b + 2) (hyb : y < b + 2) (hzb : z < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) (hzc : z < c + 2) :
    theoremCode (certificate (addAt_base_alpha b c x y z hxb hyb hzb hxc hyc hzc).forward) =
      imp (addAt b x y z).encode (addAt c x y z).encode := certificate_correct _

theorem addAt_base_backward_certificate (b c x y z : Nat)
    (hxb : x < b + 2) (hyb : y < b + 2) (hzb : z < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) (hzc : z < c + 2) :
    theoremCode (certificate (addAt_base_alpha b c x y z hxb hyb hzb hxc hyc hzc).backward) =
      imp (addAt c x y z).encode (addAt b x y z).encode := certificate_correct _

end PASoundness.PAtoCompactAddBaseMultiAlpha

#print axioms PASoundness.PAtoCompactAddBaseMultiAlpha.addAt_name_bound
#print axioms PASoundness.PAtoCompactAddBaseMultiAlpha.addAt_old_not_free
#print axioms PASoundness.PAtoCompactAddBaseMultiAlpha.addAt_new_not_names
#print axioms PASoundness.PAtoCompactAddBaseMultiAlpha.add_initial_safe
#print axioms PASoundness.PAtoCompactAddBaseMultiAlpha.addAt_disjoint_alpha
#print axioms PASoundness.PAtoCompactAddBaseMultiAlpha.addAt_base_alpha
#print axioms PASoundness.PAtoCompactAddBaseMultiAlpha.addAt_base_forward_certificate
#print axioms PASoundness.PAtoCompactAddBaseMultiAlpha.addAt_base_backward_certificate
