import Sude.FWBridgeSeedCoverage
import Sude.FWWideLayerPacking

/-! Combine the same FW graph, bridge and seed witnesses with the selected
wide role supply. Analytic inputs, seed quota, numerical mean and capacity
remain explicit hypotheses. Later controller stages are not constructed. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- On one square, install the selected bridge, retained seed and wide roles,
using the same graph for all three layer systems. -/
theorem bmor_fw_bridge_seed_wide_full_placement
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (n L : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hrect : 5 * (4 * 6) ≤ L) (hseedrect : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (otherChoice : Fin L → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card)
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ (Lucas.poolTotal n : ℝ) / (n*n : ℕ))
    (hmhi : (Lucas.poolTotal n : ℝ) / (n*n : ℕ) ≤ (123 / 250 : ℝ) * (poolMaximum n : ℝ)) :
    let choice := fwBridgeSeedRectangleChoice hrect hseedrect (fwWideRectangleChoice hwide otherChoice)
    let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
    let m : ℝ := (Lucas.poolTotal n : ℝ) / (n*n : ℕ)
    let low := bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    let high := bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    ∃ p : Fin 3 → Equiv.Perm (Fin n),
      (∀ i v, p i v ≠ v) ∧
      (∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
        500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card) ∧
    ∃ (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j),
      (∀ i < 5, ∀ j < 5, i ≠ j →
        Disjoint (doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i))
          (doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j))) ∧
      (∀ j ≤ 5, (priorBridgeReservation ∅ (Finset.range j) batches).card ≤
        (∅ : Finset ℕ).card + j * (4 * (3 * (n + 8)))) ∧
    ∃ (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
      (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16),
      candidates ⊆ seeds ∧
      (let w := sortedSeedReal candidates 17 (6 * (n + 8)) hcard
       ∃ z : ℝ, (∃ i ∈ kept, z = w (i * (6 * (n + 8)) + (6 * (n + 8) - 1)) - w (i * (6 * (n + 8)))) ∧
        (∀ i ∈ kept, w (i * (6 * (n + 8)) + (6 * (n + 8) - 1)) - w (i * (6 * (n + 8))) ≤ z) ∧
        3 * 6 * (∑ i ∈ kept, (w (i * (6 * (n + 8)) + (6 * (n + 8) - 1)) - w (i * (6 * (n + 8)))) ^ 2) + 4 * z ^ 2 ≤
          (11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2) ∧
      Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard) ∧
      (∀ x, sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard x ∈
        poolFinset n \ priorBridgeReservation ∅ (Finset.range 5) batches) ∧
    ∃ (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
      (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
      (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
      (hwc : wc.length = (3 * (n / 450)) * 3)
      (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
      (final : Cell n ≃ Fin (n*n)),
      rows.map Prod.fst = bridgeRepeatedPermutations 5 p ∧
      cols.map Prod.fst = bridgeRepeatedPermutations 5 p ∧
      sr.map Prod.fst = bridgeRepeatedPermutations 16 p ∧
      sc.map Prod.fst = bridgeRepeatedPermutations 16 p ∧
      wr.map Prod.fst = bridgeRepeatedPermutations (3 * (n / 450)) p ∧
      wc.map Prod.fst = bridgeRepeatedPermutations (3 * (n / 450)) p ∧
      LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows) (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      LayerPacking.PackedLayers
        ((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols)) sr ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr)) sc ∧
      Disjoint (LayerPacking.layersSupport sr) (LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∧
      (let base := (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport sc)
       LayerPacking.PackedLayers base wr ∧
       LayerPacking.PackedLayers (LayerPacking.transposeCells (base ∪ LayerPacking.layersSupport wr)) wc ∧
       Disjoint (LayerPacking.layersSupport wr) (LayerPacking.transposeCells (LayerPacking.layersSupport wc)) ∧
       (∀ z ∈ LayerPacking.layersSupport wr, z ∉ base ∧ z ∉ mainCells n ∧ z ∉ antiCells n) ∧
       (∀ z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport wc),
         z ∉ base ∧ z ∉ mainCells n ∧ z ∉ antiCells n)) ∧
      (∀ (j : Fin 16) (k : Fin 3) (e : Fin n),
        (sr.get (bridgeStageLayerIndex hsr j k)).1 e = p k e ∧
        (sc.get (bridgeStageLayerIndex hsc j k)).1 e = p k e) ∧
      (∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n),
        (wr.get (bridgeStageLayerIndex hwr j k)).1 e = p k e ∧
        (wc.get (bridgeStageLayerIndex hwc j k)).1 e = p k e) ∧
      (∀ t side, entry final (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
        fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t, side))) ∧
      (∀ x, entry final (fwBridgeLayerCells rows cols hr hc x) =
        fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x)) ∧
      (∀ x : Fin (16 * (4 * 6)) × Fin 4,
        entry final (packedRectangleCorner hs choice (fwSeedRectangle hseedrect x.1, x.2)) =
          sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
            (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (prefixRectangleInput hdiag x))) ∧
      (∀ x, entry final (fwSeedOrdinaryCells sr sc hsr hsc x) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x))) ∧
      (∀ block ∈ blocks, block.MatchedValid low high) ∧
      blocks.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ block ∈ blocks, Disjoint block.footprint
        (fwBridgeSeedProtectedValues batches candidates hcard kept hsub)) ∧
      (∀ x : FWWideInputs n,
        entry final (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
          doublePairSequenceEndpoint blocks
            (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2)) ∧
      (let cells : Fin blocks.length × Fin 4 → Cell n := fun x =>
        fwWidePhysicalCells hwide hs choice wr wc hwr hwc
          ((Equiv.ofBijective (fwWideFlatSlot n) (fwWideFlatSlot_bijective n)).symm
            (Fin.cast hlen x.1, x.2))
       fwInstalledPairBounds m (poolMaximum n) blocks final cells ∧
       ∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        entry final (cells (i, 1)) = entry final (cells (i, 0)) + gap ∧
        entry final (cells (i, 2)) = entry final (cells (i, 3)) + gap ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n) := by
  dsimp only
  let choice := fwBridgeSeedRectangleChoice hrect hseedrect (fwWideRectangleChoice hwide otherChoice)
  obtain ⟨p, hder, hexp, batches, hvalid, hdisjoint, hbudget, candidates, hcard, hcand,
    kept, hsub, hkept, hvariance, hinj, hav, rows, cols, hr, hc, b, hrmap, hcmap,
    hrpacked, hcpacked, hbridgeDiag0, hbridgeOrd0, hseedDiag0, hseedGap0,
    sr, sc, hsr, hsc, old, hsrmap, hscmap, hsrpacked, hscpacked,
    hsdisjoint, hends, hbridgeDiag, hbridgeOrd, hseedDiag, hseedOrd, hseedGap, hseedOrdGap⟩ :=
    bmor_fw_bridge_and_seed_full_placement bmor upper lower n L hnlo hnhi hrect hseedrect hs
      (fwWideRectangleChoice hwide otherChoice) a seeds hseed hprime hcount
  let base := (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport sc)
  have hcov := fw_bridge_seed_protected_covered batches hvalid candidates hcard kept hsub hkept hinj
    hrect hseedrect hs choice rows cols hr hc sr sc hsr hsc old hbridgeDiag hbridgeOrd hseedDiag hseedOrd
  have hprior : protectedPoolCells old (fwBridgeSeedProtectedValues batches candidates hcard kept hsub) ⊆ base :=
    hcov.trans (fw_bridge_seed_role_images_subset_base hrect hseedrect hs choice rows cols hr hc sr sc hsr hsc)
  have hdiagfree : ∀ x : Fin ((3 * (n / 450)) * (4 * 6)) × Fin 4,
      packedRectangleCorner hs choice (fwWideRectangle hwide x.1, x.2) ∉
        protectedPoolCells old (fwBridgeSeedProtectedValues batches candidates hcard kept hsub) := by
    intro x hx
    exact fw_wide_corner_avoids_bridge_seed_roles hrect hseedrect hwide hs choice rows cols hr hc
      hrpacked hcpacked sr sc hsr hsc hsrpacked hscpacked hsdisjoint x (hcov hx)
  have hrectbase : packedRectangleSupport hs choice ⊆ base := by
    intro c hc'
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hc')))
  obtain ⟨_, _, wr, wc, hwr, hwc, hwrmap, hwcmap, hwrpacked, hwcpacked, hwdisj, hwrsafe, hwcsafe, hwideEnds⟩ :=
    fw_pack_wide_layers_after_bridge_seed hnlo hs choice p hder rows cols sr sc hr hc hsr hsc
      hrpacked hcpacked hsrpacked hscpacked
  obtain ⟨blocks, hlen, final, hmatched, hpair, havoid, hfixed, hroles, _, hbounds⟩ :=
    fw_select_wide_roles_preserving_bridge_seed bmor upper lower sharp hnlo hnhi
      ((Lucas.poolTotal n : ℝ) / (n*n : ℕ)) rfl hmlo hmhi batches hvalid candidates hcard kept hsub hkept hinj
      hwide hs choice old base ∅ hrectbase hprior hdiagfree wr wc hwr hwc hwrpacked hwcpacked hwdisj
      (by intro x; simp)
  have hseedMem (x : (Fin 16 × Fin (6 * (n + 8))) × Bool) :
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept x) ∈
          retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub := by
    rw [← retainedSeedSlot_image candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept hinj]
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hBD : ∀ t side, entry final (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      entry old (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) := by
    intro t side
    apply hfixed
    rw [hbridgeDiag t side]
    exact Finset.mem_union_left _ (fwBridgeStageEndpoint_mem_final_reservation n batches hvalid _)
  have hBO : ∀ x, entry final (fwBridgeLayerCells rows cols hr hc x) =
      entry old (fwBridgeLayerCells rows cols hr hc x) := by
    intro x
    apply hfixed
    rw [hbridgeOrd x]
    exact Finset.mem_union_left _ (fwBridgeStageEndpoint_mem_final_reservation n batches hvalid _)
  have hSD : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      entry final (packedRectangleCorner hs choice (fwSeedRectangle hseedrect x.1, x.2)) =
        entry old (packedRectangleCorner hs choice (fwSeedRectangle hseedrect x.1, x.2)) := by
    intro x
    apply hfixed
    rw [hseedDiag x]
    exact Finset.mem_union_right _ (hseedMem _)
  have hSO : ∀ x, entry final (fwSeedOrdinaryCells sr sc hsr hsc x) =
      entry old (fwSeedOrdinaryCells sr sc hsr hsc x) := by
    intro x
    apply hfixed
    rw [hseedOrd x]
    exact Finset.mem_union_right _ (hseedMem _)
  have hbrdisj : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
    apply Finset.disjoint_left.mpr
    intro c hc' hd'
    exact (hcpacked.transposed_support_safe c hd').1 (Finset.mem_union_right _ hc')
  refine ⟨p, hder, hexp, batches, hvalid, hdisjoint, hbudget, candidates, hcard, kept, hsub, hkept, hcand, hvariance, hinj, hav,
    rows, cols, hr, hc, sr, sc, hsr, hsc, wr, wc, hwr, hwc, blocks, hlen, final,
    hrmap, hcmap, hsrmap, hscmap, hwrmap, hwcmap,
    hrpacked, hcpacked, hbrdisj, hsrpacked, hscpacked, hsdisjoint,
    ⟨hwrpacked, hwcpacked, hwdisj, hwrsafe, hwcsafe⟩, hends, hwideEnds,
    ?_, ?_, ?_, ?_, hmatched, hpair, havoid, hroles, hbounds⟩
  · intro t side
    exact (hBD t side).trans (hbridgeDiag t side)
  · intro x
    exact (hBO x).trans (hbridgeOrd x)
  · intro x
    exact (hSD x).trans (hseedDiag x)
  · intro x
    exact (hSO x).trans (hseedOrd x)

end
end Sude
