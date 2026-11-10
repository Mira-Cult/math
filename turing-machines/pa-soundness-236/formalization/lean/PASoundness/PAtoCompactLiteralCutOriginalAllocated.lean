import PASoundness.PAtoCompactLiteralCutNoShadow
import PASoundness.PAtoCompactLiteralCutBaseSyntax
import PASoundness.PAtoCompactAdditionZeroAllocated

/-! Capture-safe transport of the original literal-cut addition syntax into
its allocated private binder block. This is a finite K alpha equivalence;
it does not assert an addition witness or multiplication totality. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutOriginalAllocated
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactLiteralCutAdditionDefinition
open PASoundness.PAtoCompactLiteralCutNoShadow PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.PAtoCompactAdditionZeroAllocated PASoundness.PAtoCompactAddBaseInventory
open PASoundness.PAtoCompactAddBaseSyntax PASoundness.PAtoCompactMultiAlpha
open PASoundness.PAtoCompactSafeStepsInitial PASoundness.PAtoCompactEquivStepsSyntax
open PASoundness.PAtoCompactMapNamesCongr

private theorem literal_safe (b : Nat) (hb : 38 ≤ b) : InitialSafe (oldSteps b) literalTemplate := by
  refine ⟨?_, ?_, literal_allNoShadow⟩
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    have hl := addOffsets_lt k hk
    simp only [literal_free, literal_names, Finset.mem_insert, Finset.mem_singleton, not_or]
    simp [addOffsets] at hk
    omega
  · have hn : addOffsets.Nodup := by decide
    have hi : Function.Injective (fun k : Nat => b + 2 + k) := by
      intro x y h
      change b + 2 + x = b + 2 + y at h
      omega
    simpa [oldSteps, List.map_map, Function.comp_def] using List.Nodup.map hi hn

private theorem literal_shape (b : Nat) (hb : 38 ≤ b) :
    renameSteps (oldSteps b) literalTemplate = literalCutAt b 30 31 32 := by
  rw [renameSteps_eq_map]
  unfold literalCutAt
  change mapNames (applySteps (oldSteps b)) literalTemplate =
    mapNames (threeMap b 30 31 32 30 31 32) literalTemplate
  apply mapNames_congr
  intro k hk
  have hs := literalCut_names_subset hk
  simp only [Finset.mem_insert, List.mem_toFinset] at hs
  rcases hs with rfl | rfl | rfl | hs
  · simpa [threeMap] using step_fix b 30 (Or.inl rfl)
  · simpa [threeMap] using step_fix b 31 (Or.inr (Or.inl rfl))
  · simpa [threeMap] using step_fix b 32 (Or.inr (Or.inr rfl))
  · have h30 : k ≠ 30 := by simp [addOffsets] at hs; omega
    have h31 : k ≠ 31 := by simp [addOffsets] at hs; omega
    have h32 : k ≠ 32 := by simp [addOffsets] at hs; omega
    simpa [threeMap, h30,h31,h32] using step_hit b k hb hs

/-- Under the displayed bound, K proves both directions between the original
literal-cut formula and its allocated form; parameter labels remain fixed. -/
def original_allocated_alpha (b : Nat) (hb : 38 ≤ b) :
    ProofEquiv literalCut (literalCutAt b 30 31 32) := by
  have h := multiAlpha (oldSteps b) literalTemplate
    (initial_safe_steps _ _ (literal_safe b hb))
  rw [literal_shape b hb] at h
  have hn : literalTemplate = literalCut := by decide
  simpa only [hn] using h

end PASoundness.PAtoCompactLiteralCutOriginalAllocated
#print axioms PASoundness.PAtoCompactLiteralCutOriginalAllocated.original_allocated_alpha
