import Sude.FWBridgeRoleValueCoverage
import Sude.FWWideRoleValueCoverage
import Sude.BTGrowingRoleValueCoverage
import Sude.FWGrowthEarlyValues

/-! Same-square value coverage of bridge, seed, wide and growth roles.
No existence, inter-family disjointness, or preservation is asserted. -/
namespace Sude
noncomputable section

/-- Seed role values cover the retained endpoints under the two placement equations. -/
theorem fw_seed_role_values_eq_retained {n L : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (a : Cell n ≃ Fin (n*n))
    (hsd : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      entry a (packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (prefixRectangleInput (by omega) x)))
    (hso : ∀ x, entry a (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x))) :
    ((Finset.univ.image (fun x : Fin (16 * (4 * 6)) × Fin 4 =>
      packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) ∪
      Finset.univ.image (fwSeedOrdinaryCells sr sc hsr hsc)).image (entry a)) =
    retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub := by
  classical
  let cells : PrefixPhysicalInputs 16 6 3 n → Cell n :=
    Sum.elim (fun x => packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2))
      (fwSeedOrdinaryCells sr sc hsr hsc)
  have hp : ∀ x : PrefixPhysicalInputs 16 6 3 n, entry a (cells x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept
          (prefixPhysicalInput (by omega) (by omega) x)) := by
    intro x
    rcases x with x | (x | x)
    · exact hsd x
    · exact hso (Sum.inl x)
    · exact hso (Sum.inr x)
  have himage := (prefixPhysical_realizes_retained candidates 17 16 (6 * (n + 8)) 2 6 3 n
      hcard kept hsub hkept hinj (by omega) (by omega) (by omega) cells (entry a) hp).2
  have hcells : Finset.univ.image cells =
      Finset.univ.image (fun x : Fin (16 * (4 * 6)) × Fin 4 =>
        packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) ∪
      Finset.univ.image (fwSeedOrdinaryCells sr sc hsr hsc) := by
    ext c
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨x, rfl⟩
      cases x with
      | inl x => exact Or.inl ⟨x, rfl⟩
      | inr x => exact Or.inr ⟨x, rfl⟩
    · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · exact ⟨Sum.inl x, rfl⟩
      · exact ⟨Sum.inr x, rfl⟩
  rw [← hcells, Finset.image_image]
  exact himage

/-- The value image of the supplied actual role cells is the union of the
corresponding supplied early reservations and growth footprints, when all
placement and seed-image equations hold on the same square. -/
theorem fw_role_values_eq_early_and_growth {n L P Q g : ℕ}
    {initial final : Finset ℕ} {R last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial R final last stages)
    (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ Q) (hdiag : (4 * 6) * 2 ≤ Q)
    (hexact : (4 * 6) * 2 + 2 * (3 * n) = Q)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17)
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
    (a : Cell n ≃ Fin (n * n))
    (hbd : ∀ t side, entry a (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hbo : ∀ x, entry a (fwBridgeLayerCells br bc hbr hbc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    (hseedImage : ((Finset.univ.image (fun x : Fin (16 * (4 * 6)) × Fin 4 =>
      packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) ∪
      Finset.univ.image (fwSeedOrdinaryCells sr sc hsr hsc)).image (entry a)) =
        retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub)
    (hwp : ∀ x : FWWideInputs n, entry a (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlenBlocks.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (hgp : ∀ x : PrefixPhysicalInputs P 6 3 n,
      entry a (btGrowingOffsetCells (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
        hoff hs choice gr gc hgr hgc x) = (trace.poolValues hlen hpool (prefixPhysicalInput hfit hdiag x)).val) :
    (fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)).image (entry a) =
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks ∪
        Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint) := by
  classical
  have hb := fw_bridge_role_values_eq_reservation hrect hs choice batches hvalid br bc hbr hbc a hbd hbo
  have hw := fw_wide_role_values_eq_batch hwide hs choice wr wc hwr hwc blocks hlenBlocks a hwp
  have hg := bt_growing_role_values_eq_footprints trace hlen hpool hfit hdiag hexact
    (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc a hgp
  rw [fwGrowthEarlyRoleCells, Finset.image_union, Finset.image_union, Finset.image_union,
    hb, hseedImage, hw, hg]
  rfl

end
end Sude
