import PASoundness.PAtoCompactSuccBaseInventory
import PASoundness.PAtoCompactSuccBaseSyntax
import PASoundness.PAtoCompactSafeStepsInitial
import PASoundness.PAtoCompactFreeNames

/-! K alpha transport of the successor template between private allocator
blocks, subject to the explicit source-label freshness bounds. -/
namespace PASoundness.PAtoCompactSuccBaseMultiAlpha

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactMultiAlpha
open PASoundness.PAtoCompactSafeStepsInitial PASoundness.PAtoCompactSuccBaseInventory
open PASoundness.PAtoCompactSuccBaseSyntax

theorem succAt_name_bound (b x y z : Nat) (h : z ∈ (succAt b x y).names) :
    z = x ∨ z = y ∨ (b + 2 ≤ z ∧ z < b + 40) := by
  unfold succAt at h
  rw [mapNames_names] at h
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp h
  have hkbound := templates_names_bounded.2.2.2.1 hk
  simp only [Finset.mem_range] at hkbound
  by_cases hk0 : k = 0
  · left; simpa [twoMap, hk0] using he.symm
  · by_cases hk1 : k = 1
    · right; left; simpa [twoMap, hk0, hk1] using he.symm
    · right; right
      simp [twoMap, hk0, hk1] at he
      omega

theorem succAt_old_not_free (b x y k : Nat) (hx : x < b + 2) (hy : y < b + 2) :
    b + 2 + k ∉ (succAt b x y).free := by
  intro h
  have hh := succAt_free b x y h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with h | h <;> omega

theorem succAt_new_not_names (b c x y k : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hdis : b + 39 < c + 2) :
    c + 2 + k ∉ (succAt b x y).names := by
  intro h
  rcases succAt_name_bound b x y _ h with h | h | h <;> omega

theorem succ_initial_safe (b c x y : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hdis : b + 39 < c + 2) :
    InitialSafe (succSteps b c) (succAt b x y) := by
  refine ⟨?_, ?_, succAt_allNoShadow b x y⟩
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact ⟨by simp only; omega, succAt_old_not_free b x y k hx hy,
      succAt_new_not_names b c x y k hx hy hdis⟩
  · have hn : succOffsets.Nodup := by decide
    have hi : Function.Injective (fun k : Nat => c + 2 + k) := by
      intro i j he
      change c + 2 + i = c + 2 + j at he
      omega
    have hm := List.Nodup.map hi hn
    simpa [succSteps, List.map_map, Function.comp_def] using hm

/-- Move all successor-template binders between disjoint blocks by finite K
alpha proofs; source operand labels may coincide. -/
def succAt_disjoint_alpha (b c x y : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hdis : b + 39 < c + 2) :
    ProofEquiv (succAt b x y) (succAt c x y) := by
  have hs := initial_safe_steps (succSteps b c) (succAt b x y)
    (succ_initial_safe b c x y hx hy hdis)
  have h := multiAlpha (succSteps b c) (succAt b x y) hs
  rw [renameSteps_succAt b c x y hdis hx hy] at h
  exact h

/-- A third block handles overlapping source and target allocations. -/
def succAt_base_alpha (b c x y : Nat)
    (hxb : x < b + 2) (hyb : y < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) :
    ProofEquiv (succAt b x y) (succAt c x y) := by
  let d := max b c + 100
  have hbd : b + 39 < d + 2 := by dsimp [d]; omega
  have hcd : c + 39 < d + 2 := by dsimp [d]; omega
  exact (succAt_disjoint_alpha b d x y hxb hyb hbd).trans
    (succAt_disjoint_alpha c d x y hxc hyc hcd).symm

theorem succAt_base_forward_certificate (b c x y : Nat)
    (hxb : x < b + 2) (hyb : y < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) :
    theoremCode (certificate (succAt_base_alpha b c x y hxb hyb hxc hyc).forward) =
      imp (succAt b x y).encode (succAt c x y).encode := certificate_correct _

theorem succAt_base_backward_certificate (b c x y : Nat)
    (hxb : x < b + 2) (hyb : y < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) :
    theoremCode (certificate (succAt_base_alpha b c x y hxb hyb hxc hyc).backward) =
      imp (succAt c x y).encode (succAt b x y).encode := certificate_correct _

end PASoundness.PAtoCompactSuccBaseMultiAlpha

#print axioms PASoundness.PAtoCompactSuccBaseMultiAlpha.succAt_name_bound
#print axioms PASoundness.PAtoCompactSuccBaseMultiAlpha.succAt_old_not_free
#print axioms PASoundness.PAtoCompactSuccBaseMultiAlpha.succAt_new_not_names
#print axioms PASoundness.PAtoCompactSuccBaseMultiAlpha.succ_initial_safe
#print axioms PASoundness.PAtoCompactSuccBaseMultiAlpha.succAt_disjoint_alpha
#print axioms PASoundness.PAtoCompactSuccBaseMultiAlpha.succAt_base_alpha
#print axioms PASoundness.PAtoCompactSuccBaseMultiAlpha.succAt_base_forward_certificate
#print axioms PASoundness.PAtoCompactSuccBaseMultiAlpha.succAt_base_backward_certificate
