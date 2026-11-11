import Sude.BTGrowingPoolValues

/-! Exact set coverage of the endpoints in a supplied growing trace. -/
namespace Sude
noncomputable section

/-- The pool values indexed by stage, pair and side cover exactly the union of
stage footprints. Empty stage or pair index types are allowed. -/
theorem BTGrowingTrace.poolValues_image_eq_footprints
    {g Q n : ℕ} {initial final : Finset ℕ} {R last : ℕ}
    {stages : List BTSelectedStage} (trace : BTGrowingTrace g Q initial R final last stages)
    {P : ℕ} (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n) :
    (Finset.univ : Finset ((Fin P × Fin Q) × Bool)).image
      (fun x => (trace.poolValues hlen hpool x).val) =
    Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint) := by
  classical
  have hlows (j : Fin P) : Finset.univ.image (trace.lowAt hlen j) =
      (BTStageTrace.stageAt stages hlen j).lows := by
    exact Finset.image_orderEmbOfFin_univ _ _
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨⟨j, i⟩, side⟩, rfl⟩
    refine ⟨j, ?_⟩
    have hm := trace.lowAt_mem hlen j i
    cases side <;> simp [BTGrowingTrace.poolValues, BTSelectedStage.footprint, pairFootprint, hm]
  · rintro ⟨j, hv⟩
    simp only [BTSelectedStage.footprint, pairFootprint, Finset.mem_union, Finset.mem_image] at hv
    rcases hv with hv | ⟨a, ha, rfl⟩
    · have hm : v ∈ Finset.univ.image (trace.lowAt hlen j) := by rw [hlows]; exact hv
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
      exact ⟨((j, i), false), by simpa [BTGrowingTrace.poolValues] using hi⟩
    · have hm : a ∈ Finset.univ.image (trace.lowAt hlen j) := by rw [hlows]; exact ha
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
      exact ⟨((j, i), true), by simp [BTGrowingTrace.poolValues, hi]⟩

end
end Sude
