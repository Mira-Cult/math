import Sude.FWRoleValueUnion

/-! Transfer early physical placements to a growth square that preserves the
actual early role cells, then identify the complete role-value union. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- Under the supplied old-square placements and preservation of all actual
early role cells, the grown square realizes the early reservations and actual
growth footprints at the combined role cells. -/
theorem fw_grown_role_values_eq_early_and_growth {n L P Q g : ℕ}
    {initial final : Finset ℕ} {R last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial R final last stages)
    (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ Q) (hdiag : (4 * 6) * 2 ≤ Q)
    (hexact : (4 * 6) * 2 + 2 * (3 * n) = Q)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hlenBlocks : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (old grown : Cell n ≃ Fin (n * n))
    (hkeep : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hbd : ∀ t side, entry old (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hbo : ∀ x, entry old (fwBridgeLayerCells br bc hbr hbc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    (hsd : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      entry old (packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (prefixRectangleInput (by omega) x)))
    (hso : ∀ x, entry old (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x)))
    (hwp : ∀ x : FWWideInputs n, entry old (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlenBlocks.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (hgp : ∀ x : PrefixPhysicalInputs P 6 3 n,
      entry grown (btGrowingOffsetCells (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
        hoff hs choice gr gc hgr hgc x) = (trace.poolValues hlen hpool (prefixPhysicalInput hfit hdiag x)).val) :
    (fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)).image (entry grown) =
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks ∪
        Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint) := by
  classical
  have hbmem (t : Fin (5 * (4 * 6))) (side : Fin 4) :
      packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side) ∈
        fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(t, side), Finset.mem_univ _, rfl⟩
  have hbomem (x : (Fin 5 × (Fin 3 × Fin n)) × (Bool × Bool)) :
      fwBridgeLayerCells br bc hbr hbc x ∈
        fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hsdmem (x : Fin (16 * (4 * 6)) × Fin 4) :
      packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2) ∈
        fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc := by
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hsomem (x : FWSeedOrdinaryInputs n) : fwSeedOrdinaryCells sr sc hsr hsc x ∈
        fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc := by
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hwpmem (x : FWWideInputs n) : fwWidePhysicalCells hwide hs choice wr wc hwr hwc x ∈
        fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc := by
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hbd' t side := (hkeep _ (hbmem t side)).trans (hbd t side)
  have hbo' x := (hkeep _ (hbomem x)).trans (hbo x)
  have hsd' x := (hkeep _ (hsdmem x)).trans (hsd x)
  have hso' x := (hkeep _ (hsomem x)).trans (hso x)
  have hwp' x := (hkeep _ (hwpmem x)).trans (hwp x)
  have hseedImage := fw_seed_role_values_eq_retained candidates hcard kept hsub hkept hinj
    hseed hs choice sr sc hsr hsc grown hsd' hso'
  exact fw_role_values_eq_early_and_growth trace hlen hpool hfit hdiag hexact
    batches hvalid candidates hcard kept hsub blocks hlenBlocks hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc grown hbd' hbo' hseedImage hwp' hgp

end
end Sude
