import PASoundness.PAtoCompactLiteralCutBaseSyntax
import PASoundness.PAtoCompactLiteralCutNoShadow
import PASoundness.PAtoCompactAddBaseMultiAlpha

/-! K alpha transport of the literal-cut addition relation across allocation
bases. All operand labels may coincide; their stated bounds keep them outside
both private binder blocks. This is not an existence proof. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutBaseAlpha
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactMultiAlpha
open PASoundness.PAtoCompactSafeStepsInitial PASoundness.PAtoCompactAddBaseSyntax
open PASoundness.PAtoCompactLiteralCutBaseSyntax PASoundness.PAtoCompactLiteralCutNoShadow

/-- Every name is either a parameter or is allocated in the private block. -/
theorem literalCutAt_name_bound (b x y z w : Nat)
    (h : w ∈ (literalCutAt b x y z).names) :
    w = x ∨ w = y ∨ w = z ∨ (b+2 ≤ w ∧ w < b+40) := by
  unfold literalCutAt at h
  rw [mapNames_names] at h
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp h
  have hkbound : k < 38 := by
    change k ∈ literalTemplate.names at hk
    rw [literal_names] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  by_cases hk30 : k = 30
  · left; simpa [threeMap, hk30] using he.symm
  · by_cases hk31 : k = 31
    · right; left; simpa [threeMap, hk30, hk31] using he.symm
    · by_cases hk32 : k = 32
      · right; right; left; simpa [threeMap, hk30, hk31, hk32] using he.symm
      · right; right; right
        simp [threeMap, hk30, hk31, hk32] at he
        omega

/-- Only the three displayed parameters may occur freely. -/
theorem literalCutAt_free (b x y z : Nat) : (literalCutAt b x y z).free ⊆ {x,y,z} := by
  unfold literalCutAt
  refine (mapNames_free_subset _ _).trans ?_
  apply Finset.image_subset_iff.mpr
  intro a ha
  change a ∈ literalTemplate.free at ha
  rw [literal_free] at ha
  have hh : a = 30 ∨ a = 31 ∨ a = 32 := by simpa using ha
  rcases hh with rfl | rfl | rfl <;> simp [threeMap]

theorem old_not_free (b x y z k : Nat)
    (hx : x < b+2) (hy : y < b+2) (hz : z < b+2) :
    b+2+k ∉ (literalCutAt b x y z).free := by
  intro h
  have hh := literalCutAt_free b x y z h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with h | h | h <;> omega

theorem new_not_names (b c x y z k : Nat)
    (hx : x < b+2) (hy : y < b+2) (hz : z < b+2)
    (hdis : b+39 < c+2) : c+2+k ∉ (literalCutAt b x y z).names := by
  intro h
  rcases literalCutAt_name_bound b x y z _ h with h | h | h | h <;> omega

theorem initial_safe (b c x y z : Nat)
    (hx : x < b+2) (hy : y < b+2) (hz : z < b+2)
    (hdis : b+39 < c+2) : InitialSafe (addSteps b c) (literalCutAt b x y z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact ⟨by simp only; omega, old_not_free b x y z k hx hy hz,
      new_not_names b c x y z k hx hy hz hdis⟩
  · have hn : addOffsets.Nodup := by decide
    have hi : Function.Injective (fun k : Nat => c+2+k) := by
      intro i j he
      change c+2+i = c+2+j at he
      omega
    have hm := List.Nodup.map hi hn
    simpa [addSteps, List.map_map, Function.comp_def] using hm
  · intro w
    simpa [literalCutAt, literalTemplate] using literal_mapped_allNoShadow b x y z w

/-- K alpha conversion for non-overlapping allocator blocks. -/
def disjoint_alpha (b c x y z : Nat)
    (hx : x < b+2) (hy : y < b+2) (hz : z < b+2)
    (hdis : b+39 < c+2) : ProofEquiv (literalCutAt b x y z) (literalCutAt c x y z) := by
  have hs := initial_safe_steps (addSteps b c) (literalCutAt b x y z)
    (initial_safe b c x y z hx hy hz hdis)
  have h := multiAlpha (addSteps b c) (literalCutAt b x y z) hs
  rw [renameSteps_literalCutAt b c x y z hdis hx hy hz] at h
  exact h

/-- K alpha conversion for arbitrary allocator blocks via a fresh third block. -/
def base_alpha (b c x y z : Nat)
    (hxb : x < b+2) (hyb : y < b+2) (hzb : z < b+2)
    (hxc : x < c+2) (hyc : y < c+2) (hzc : z < c+2) :
    ProofEquiv (literalCutAt b x y z) (literalCutAt c x y z) := by
  let d := max b c + 100
  have hbd : b+39 < d+2 := by dsimp [d]; omega
  have hcd : c+39 < d+2 := by dsimp [d]; omega
  exact (disjoint_alpha b d x y z hxb hyb hzb hbd).trans
    (disjoint_alpha c d x y z hxc hyc hzc hcd).symm

theorem base_alpha_forward_certificate (b c x y z : Nat)
    (hxb : x < b+2) (hyb : y < b+2) (hzb : z < b+2)
    (hxc : x < c+2) (hyc : y < c+2) (hzc : z < c+2) :
    theoremCode (certificate (base_alpha b c x y z hxb hyb hzb hxc hyc hzc).forward) =
      imp (literalCutAt b x y z).encode (literalCutAt c x y z).encode := certificate_correct _

theorem base_alpha_backward_certificate (b c x y z : Nat)
    (hxb : x < b+2) (hyb : y < b+2) (hzb : z < b+2)
    (hxc : x < c+2) (hyc : y < c+2) (hzc : z < c+2) :
    theoremCode (certificate (base_alpha b c x y z hxb hyb hzb hxc hyc hzc).backward) =
      imp (literalCutAt c x y z).encode (literalCutAt b x y z).encode := certificate_correct _
end PASoundness.PAtoCompactLiteralCutBaseAlpha
#print axioms PASoundness.PAtoCompactLiteralCutBaseAlpha.literalCutAt_name_bound
#print axioms PASoundness.PAtoCompactLiteralCutBaseAlpha.literalCutAt_free
#print axioms PASoundness.PAtoCompactLiteralCutBaseAlpha.initial_safe
#print axioms PASoundness.PAtoCompactLiteralCutBaseAlpha.base_alpha
#print axioms PASoundness.PAtoCompactLiteralCutBaseAlpha.base_alpha_forward_certificate
#print axioms PASoundness.PAtoCompactLiteralCutBaseAlpha.base_alpha_backward_certificate
