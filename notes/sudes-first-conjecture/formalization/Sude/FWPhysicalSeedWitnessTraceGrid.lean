import Sude.FWPhysicalSeedTraceGrid
import Sude.FWWheelWitnessTraceStock

/-! Physical seed labels and a supplied abstract trace using the same actual
early value witnesses. Growth stages are not physically installed. -/
namespace Sude
noncomputable section
local instance fwPhysicalSeedWitnessStageDecidable : DecidableEq BTSelectedStage := Classical.decEq _
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- The seed endpoint equations imply an actual physical seed-value grid
extended by the supplied trace, whose footprints avoid those seed values. -/
theorem fw_physical_seed_witness_trace_grid {n L : ℕ}
    (batches : ℕ → List DoublePair)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (hav : ∀ x, sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard x ∈
      poolFinset n \ priorBridgeReservation ∅ (Finset.range 5) batches)
    (blocks : List DoublePair)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (a : Cell n ≃ Fin (n*n))
    (hplaced : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      entry a (packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept
            (prefixRectangleInput (by omega) x)))
    {final : Finset ℕ} {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 final last stages) :
    let gap : Sum (ℕ × ℕ) BTSelectedStage → ℕ := Sum.elim fwPhysicalSeedLabelGap BTSelectedStage.gap
    let base := Finset.univ.image (fun i => Sum.inl (fwPhysicalSeedLabel hseed hs choice a i) :
      Fin 16 → Sum (ℕ × ℕ) BTSelectedStage)
    let labels : List (Sum (ℕ × ℕ) BTSelectedStage) := stages.map Sum.inr
    CompleteEvenGrid (base ∪ labels.toFinset) gap last ∧ 2 ∣ last ∧
    (∀ stage ∈ stages, Disjoint stage.footprint
      (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
    (∀ stage ∈ stages, ∀ i : Fin 16, ∀ side : Bool,
      entry a (fwPhysicalSeedCell hseed hs choice i side) ∉ stage.footprint) := by
  dsimp only
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  have hgap : ∀ (j : Fin 16) (u : Fin (4 * 6)) (pair : Fin 2),
      entry a (packedRectangleCorner hs choice
        (fwSeedRectangle hseed (finProdFinEquiv (j, u)), prefixPairCorner pair true)) =
      entry a (packedRectangleCorner hs choice
        (fwSeedRectangle hseed (finProdFinEquiv (j, u)), prefixPairCorner pair false)) + 2 := by
    intro j u pair
    rw [hplaced (finProdFinEquiv (j, u), prefixPairCorner pair true),
      hplaced (finProdFinEquiv (j, u), prefixPairCorner pair false)]
    rw [prefixRectangleInput_pair, prefixRectangleInput_pair]
    exact retainedSeedPoolValues_gap candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept
      (priorBridgeReservation ∅ (Finset.range 5) batches) hav j (prefixDiagonalPairIndex hdiag (u, pair))
  obtain ⟨hgrid, heven⟩ := fw_physical_seed_trace_even_grid hseed hs choice a hgap (by omega) trace
  have havoids : ∀ stage ∈ stages, Disjoint stage.footprint
      (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) := by
    intro stage hstage
    apply Finset.disjoint_left.mpr
    intro p hp hearly
    exact (Finset.mem_sdiff.mp (trace.footprints_subset stage hstage hp)).2 hearly
  refine ⟨hgrid, heven, havoids, ?_⟩
  intro stage hstage i side hp
  have hfoot := trace.footprints_subset stage hstage hp
  have hseedmem : entry a (fwPhysicalSeedCell hseed hs choice i side) ∈
      retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub := by
    dsimp [fwPhysicalSeedCell]
    rw [hplaced (finProdFinEquiv (i, (0 : Fin (4 * 6))), prefixPairCorner (0 : Fin 2) side)]
    rw [← retainedSeedSlot_image candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept hinj]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  apply (Finset.mem_sdiff.mp hfoot).2
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact hseedmem

end
end Sude
