import Sude.BTGrowingPhysicalStageTotals
import Sude.FWSeedExistingReallocation

/-! Same-square physical separation of supplied seed and growth cells by
their disjoint value sets. No theta existence or line bound is asserted. -/
namespace Sude
noncomputable section

/-- If two physical images carry values from disjoint sets, the cell images
are disjoint. No injectivity of the value map is required. -/
theorem physical_images_disjoint_of_value_separation {α β γ δ : Type*}
    [Fintype α] [Fintype β] [DecidableEq γ] [DecidableEq δ]
    (seed : α → γ) (growth : β → γ) (value : γ → δ)
    (early initial : Finset δ) (hdis : Disjoint initial early)
    (hseed : ∀ x, value (seed x) ∈ early)
    (hgrowth : ∀ x, value (growth x) ∈ initial) :
    Disjoint (Finset.univ.image seed) (Finset.univ.image growth) := by
  apply Finset.disjoint_left.mpr
  intro c hc hc'
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hc
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hc'
  have hv := congrArg value (hx.trans hy.symm)
  have hearly := hseed x
  rw [hv] at hearly
  exact Finset.disjoint_left.mp hdis (hgrowth y) hearly

/-- Actual FW seed and reindexed growth pair-cell images are disjoint when
the same square places their values in the supplied disjoint stocks. Exact
growth allocation and the same-square placement are explicit hypotheses. -/
theorem fw_seed_growth_physical_pair_images_disjoint
    {g n P L : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g (6 * (n + 8)) initial radius final last stages)
    (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (early : Finset ℕ) (hdis : Disjoint initial early)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (offset : ℕ) (hoff : offset + P * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool)
    (sr sc gr gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (a : Cell n ≃ Fin (n * n))
    (hseedValues : ∀ x, entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x) ∈ early)
    (hplaced : ∀ x : PrefixPhysicalInputs P 6 3 n,
      entry a (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
        (trace.poolValues hlen hpool (prefixPhysicalInput (by omega) (by omega) x)).val) :
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc
    Disjoint (Finset.univ.image (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc))
      (Finset.univ.image growth) := by
  dsimp only
  have htotals := bt_growing_physical_stage_totals trace hlen hpool
    (by omega) (by omega) (by omega) offset hoff hs choice gr gc hgr hgc a hplaced
  have hentry := htotals.2.1
  apply physical_images_disjoint_of_value_separation _ _ (entry a) early initial hdis hseedValues
  rintro ⟨⟨j, i⟩, side⟩
  rw [hentry]
  exact trace.endpoint_mem_initial hlen j i side

end
end Sude
