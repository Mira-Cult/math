import PASoundness.PAtoCompactMulBaseMultiAlpha

/-! Literal K alpha equivalence between the original multiplication formula
and its allocated template with input labels 0, 1, and 2. This moves only
bound labels and establishes neither multiplication totality nor semantic
soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOriginalAllocatedAlpha
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMultiAlpha PASoundness.PAtoCompactSafeStepsInitial
open PASoundness.PAtoCompactMulBaseInventory PASoundness.PAtoCompactMulBaseSyntax
open PASoundness.PAtoCompactEquivStepsSyntax PASoundness.PAtoCompactMapNamesCongr

private def oldSteps (b : Nat) : List (Nat × Nat) := mulOffsets.map (fun k => (k,b+2+k))

private theorem step_fix (b z : Nat) (hz : z = 0 ∨ z = 1 ∨ z = 2) :
    applySteps (oldSteps b) z = z := by
  apply applySteps_avoid
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
  simp only
  simp [mulOffsets] at hk
  omega

private theorem step_hit (b k : Nat) (hb : 38 ≤ b) (hk : k ∈ mulOffsets) :
    applySteps (oldSteps b) k = b+2+k := by
  apply applySteps_hit
  · exact List.mem_map.mpr ⟨k,hk,rfl⟩
  · intro z hz
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hz
    have hi1 := congrArg Prod.fst he
    have hi2 := congrArg Prod.snd he
    simp only at hi1 hi2
    omega
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have hil := mulOffsets_lt i hi
    omega

private theorem old_safe (b : Nat) (hb : 38 ≤ b) :
    InitialSafe (oldSteps b) (normalizeBottom productFormula) := by
  refine ⟨?_, ?_, product_allNoShadow⟩
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    have hl := mulOffsets_lt k hk
    simp only [PAtoCompactMulBaseInventory.product_free, product_names,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    simp [mulOffsets] at hk
    omega
  · have hn : mulOffsets.Nodup := by decide
    have hi : Function.Injective (fun k : Nat => b + 2 + k) := by
      intro x y h
      change b + 2 + x = b + 2 + y at h
      omega
    simpa [oldSteps, List.map_map, Function.comp_def] using List.Nodup.map hi hn

private theorem old_shape (b : Nat) (hb : 38 ≤ b) :
    renameSteps (oldSteps b) (normalizeBottom productFormula) = mulAt b 0 1 2 := by
  rw [renameSteps_eq_map]
  unfold mulAt
  apply mapNames_congr
  intro k hk
  have hs := product_names_subset hk
  simp only [Finset.mem_insert, List.mem_toFinset] at hs
  rcases hs with rfl | rfl | rfl | hs
  · simpa [threeMap] using step_fix b 0 (Or.inl rfl)
  · simpa [threeMap] using step_fix b 1 (Or.inr (Or.inl rfl))
  · simpa [threeMap] using step_fix b 2 (Or.inr (Or.inr rfl))
  · have h0 : k ≠ 0 := by simp [mulOffsets] at hs; omega
    have h1 : k ≠ 1 := by simp [mulOffsets] at hs; omega
    have h2 : k ≠ 2 := by simp [mulOffsets] at hs; omega
    simpa [threeMap, h0,h1,h2] using step_hit b k hb hs

/-- The original product formula and its allocated version have finite K
proofs in both directions for every base at least 38. -/
noncomputable def original_allocated_alpha (b : Nat) (hb : 38 ≤ b) :
    ProofEquiv productFormula (mulAt b 0 1 2) := by
  have h := multiAlpha (oldSteps b) (normalizeBottom productFormula)
    (initial_safe_steps _ _ (old_safe b hb))
  rw [old_shape b hb] at h
  have hn : normalizeBottom productFormula = productFormula := by decide
  rw [hn] at h
  exact h

theorem original_allocated_alpha_forward_certificate (b : Nat) (hb : 38 ≤ b) :
    theoremCode (certificate (original_allocated_alpha b hb).forward) =
      imp productFormula.encode (mulAt b 0 1 2).encode := certificate_correct _

theorem original_allocated_alpha_backward_certificate (b : Nat) (hb : 38 ≤ b) :
    theoremCode (certificate (original_allocated_alpha b hb).backward) =
      imp (mulAt b 0 1 2).encode productFormula.encode := certificate_correct _
end PASoundness.PAtoCompactProductOriginalAllocatedAlpha
#print axioms PASoundness.PAtoCompactProductOriginalAllocatedAlpha.original_allocated_alpha
#print axioms PASoundness.PAtoCompactProductOriginalAllocatedAlpha.original_allocated_alpha_forward_certificate
#print axioms PASoundness.PAtoCompactProductOriginalAllocatedAlpha.original_allocated_alpha_backward_certificate
