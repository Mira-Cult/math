import Sude.FWReservedPhysicalSeedBoundedWheelGrid
import Sude.FWGrowthEarlyInstall
import Sude.FWGrowthRectangleChoice

/-! A bounded first-window trace physically installed after the early square.
No threshold crossing or later phase is asserted. -/
namespace Sude
noncomputable section
local instance fwEarlyGrowthPhysicalStageDecidable : DecidableEq BTSelectedStage := Classical.decEq _
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- The actual early and growing role families use one graph and one square.
The 238-stage bound pays for the reserved P₀=254 rectangle allowance. -/
theorem bmor_fw_early_and_growth_physical
    (piFour : BMORFinitePiFour) (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    let hrect := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).1
    let hseedrect := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).2.1
    let hwide := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).2.2.1
    let hs := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).2.2.2
    let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
    let choice := fwBridgeSeedRectangleChoice hrect hseedrect
      (fwWideRectangleChoice hwide (fwGrowthRectangleChoice hmax otherChoice))
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
      (final : Cell n ≃ Fin (n*n)) (gap : ℕ) (chosen : Finset ℕ) (width : ℝ)
      (stock : Finset ℕ) (last : ℕ) (extra : List BTSelectedStage),
      (let stages := [⟨gap, chosen, width⟩] ++ extra
       let initial := ((poolFinset n).filter (fun p => 43 < p)) \
         fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
       let hpool : ∀ v ∈ initial, v ∈ pool n := by
         intro v hv
         exact mem_poolFinset.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
       let P := stages.length
       let offset := 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)
       let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
       let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
       ∃ (htrace : BTGrowingTrace 2 (6 * (n + 8)) initial 32 stock last stages)
         (hoff : offset + P * (4 * 6) ≤ fwJointRectangleCount n 254),
       ∃ (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
      (b : Cell n ≃ Fin (n*n)),
      gr.map Prod.fst = bridgeRepeatedPermutations P p ∧
      gc.map Prod.fst = bridgeRepeatedPermutations P p ∧
      (∀ (j : Fin P) (i : Fin (4 * 6)),
        choice (btGrowingOffsetRectangle offset hoff (finProdFinEquiv (j, i))) = decide (i.val < 2 * 6)) ∧
      LayerPacking.PackedLayers (fwGrowthEarlyBase hs choice rows cols sr sc wr wc) gr ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (fwGrowthEarlyBase hs choice rows cols sr sc wr wc ∪ LayerPacking.layersSupport gr)) gc ∧
      Disjoint (LayerPacking.layersSupport gr) (LayerPacking.transposeCells (LayerPacking.layersSupport gc)) ∧
      (∀ (j : Fin P) (k : Fin 3) (e : Fin n),
        (gr.get (bridgeStageLayerIndex hgr j k)).1 e = p k e ∧
        (gc.get (bridgeStageLayerIndex hgc j k)).1 e = p k e) ∧
      (∀ c ∈ fwGrowthEarlyRoleCells hrect hseedrect hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
        entry b c = entry final c) ∧
      (let valueGap : Sum (ℕ × ℕ) BTSelectedStage → ℕ := Sum.elim fwPhysicalSeedLabelGap BTSelectedStage.gap
       let base := Finset.univ.image (fun i => Sum.inl (fwPhysicalSeedLabel hseedrect hs choice b i) :
         Fin 16 → Sum (ℕ × ℕ) BTSelectedStage)
       let labels : List (Sum (ℕ × ℕ) BTSelectedStage) := stages.map Sum.inr
       CompleteEvenGrid (base ∪ labels.toFinset) valueGap last) ∧
      (∀ x : PrefixPhysicalInputs P 6 3 n,
        entry b (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
          (htrace.poolValues (rfl : stages.length = P) hpool (prefixPhysicalInput hfit hdiag x)).val) ∧
      (∀ (j : Fin P) (u : Fin (4 * 6)) (pair : Fin 2),
        entry b (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc
          (Sum.inl (finProdFinEquiv (j, u), prefixPairCorner pair true))) =
        entry b (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc
          (Sum.inl (finProdFinEquiv (j, u), prefixPairCorner pair false))) +
            (BTStageTrace.stageAt stages (rfl : stages.length = P) j).gap) ∧
      (∀ (i : Fin (P * 3)) (e : Fin n),
        entry b (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, true))))) =
        entry b (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, false))))) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages (rfl : stages.length = P) j).gap) rfl i e) ∧
      (∀ (i : Fin (P * 3)) (e : Fin n),
        entry b (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, true))))) =
        entry b (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, false))))) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages (rfl : stages.length = P) j).gap) rfl i e) ∧
      (∀ y : (Fin P × Fin (6 * (n + 8))) × Bool, ∃ x : PrefixPhysicalInputs P 6 3 n,
        prefixPhysicalInput hfit hdiag x = y ∧
        entry b (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
          (htrace.poolValues (rfl : stages.length = P) hpool y).val)) ∧
            (let initial := ((poolFinset n).filter (fun p => 43 < p)) \
         fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
       let stages := [⟨gap, chosen, width⟩] ++ extra
       let valueGap : Sum (ℕ × ℕ) BTSelectedStage → ℕ := Sum.elim fwPhysicalSeedLabelGap BTSelectedStage.gap
       let base := Finset.univ.image (fun i => Sum.inl (fwPhysicalSeedLabel hseedrect hs choice final i) :
         Fin 16 → Sum (ℕ × ℕ) BTSelectedStage)
       let labels : List (Sum (ℕ × ℕ) BTSelectedStage) := stages.map Sum.inr
       BTGrowingTrace 2 (6 * (n + 8)) initial 32 stock last stages ∧
       stages.length ≤ 238 ∧
       ((poolMaximum n : ℝ) / 23 ≤ last ∨ stages.length = 238) ∧
       NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
       NarrowedStages ((poolMaximum n : ℝ) / 6) stages ∧
       CompleteEvenGrid (base ∪ labels.toFinset) valueGap last ∧ 2 ∣ last ∧
       (∀ stage ∈ stages, Disjoint stage.footprint
         (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
       (∀ stage ∈ stages, ∀ i : Fin 16, ∀ side : Bool,
         entry final (fwPhysicalSeedCell hseedrect hs choice i side) ∉ stage.footprint)) ∧
      (let Q := 6 * (n + 8)
       let initial := ((poolFinset n).filter (fun p => 43 < p)) \
         fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
       let m : ℝ := 403 / 10000 - 2 * (1 / 69780 : ℝ) * ([] : List BTSelectedStage).length
       let T := ⌊(3981035 / 10000000 : ℝ) * m * 32 - 1 / 2⌋₊
       let cutoff := 2 * min
         (fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
           (Nat.totient_pos.mpr (by decide))) (32 / 2)
       width = (cutoff : ℝ) ∧ width = 2 ∧ 2 ≤ gap ∧ 2 ∣ gap ∧ cutoff ≤ gap ∧ gap ≤ 32 ∧
         chosen.card = Q ∧
         (∀ p ∈ chosen, (p, p + gap) ∈ sameClassPairs initial (progressionBinKey 0 32 2)) ∧
         PairwiseDisjointPairs chosen gap ∧ pairFootprint chosen gap ⊆ initial ∧
         Disjoint (pairFootprint chosen gap)
           (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) ∧
         (pairFootprint chosen gap).card = 2 * Q ∧
         (initial \ pairFootprint chosen gap).card + 2 * Q = initial.card ∧
         (∀ p ∈ chosen, ∀ q ∈ chosen,
           |(((p : ℝ) + (p + gap : ℕ)) / 2) - (((q : ℝ) + (q + gap : ℕ)) / 2)| <
             (poolMaximum n : ℝ) / 6) ∧
         32 + cutoff ≤ 32 + gap ∧
         BTGrowingTrace 2 Q initial 32 (initial \ pairFootprint chosen gap) (32 + gap)
           [⟨gap, chosen, width⟩]) ∧
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
  let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
  obtain ⟨p, hder, hexp, batches, hvalid, hdisjoint, hbudget, candidates, hcard,
    kept, hsub, hkept, hcand, hvariance, hinj, hav, rows, cols, hr, hc,
    sr, sc, hsr, hsc, wr, wc, hwr, hwc, blocks, hlen, final, gap, chosen, width,
    stock, last, extra, hbounded, hstage, hrest⟩ :=
    bmor_fw_reserved_early_physical_seed_bounded_wheel_grid piFour bmor upper lower sharp upperSharp n 254
      hnlo hnhi (by decide) (by decide) (fwGrowthRectangleChoice hmax otherChoice) a seeds hseed hprime hcount
  let hrect := (fw_reserved_wide_rectangle_capacity hnlo (show 16 ≤ 254 by decide) (show 254 ≤ 270 by decide)).1
  let hseedrect := (fw_reserved_wide_rectangle_capacity hnlo (show 16 ≤ 254 by decide) (show 254 ≤ 270 by decide)).2.1
  let hwide := (fw_reserved_wide_rectangle_capacity hnlo (show 16 ≤ 254 by decide) (show 254 ≤ 270 by decide)).2.2.1
  let hs := (fw_reserved_wide_rectangle_capacity hnlo (show 16 ≤ 254 by decide) (show 254 ≤ 270 by decide)).2.2.2
  let choice := fwBridgeSeedRectangleChoice hrect hseedrect
    (fwWideRectangleChoice hwide (fwGrowthRectangleChoice hmax otherChoice))
  let stages := [⟨gap, chosen, width⟩] ++ extra
  let P := stages.length
  have htrace := hbounded.1
  have hcap : P ≤ 238 := hbounded.2.1
  have hoff := fw_growth_offset_rectangle_capacity (n := n) (P := P) (P₀ := 254) (by omega)
  obtain ⟨hrmap, hcmap, hsrmap, hscmap, hwrmap, hwcmap,
    hrows, hcols, hbrdisj, hsrows, hscols, hsdisj, hwpack,
    hseedEnds, hwideEnds, hbd, hbo, hsd, hso, hmatched, hpair, havoid, hwp, hbounds⟩ := hrest
  obtain ⟨hwrows, hwcols, hwdisj, hwrsafe, hwcsafe⟩ := hwpack
  obtain ⟨gr, gc, hgr, hgc, grown, hgrmap, hgcmap, hgrpacked, hgcpacked,
    hgdisj, hends, hfixed, hplaced, hdiagGap, hrowGap, hcolGap, hcomplete⟩ :=
    fw_install_growth_after_actual_early hnlo (by omega : n ≤ 35733) hcap p hder batches hvalid candidates hcard kept hsub hkept
      hinj blocks hlen hrect hseedrect hwide hoff hs choice rows cols hr hc hrows hcols sr sc hsr hsc
      hsrows hscols hsdisj wr wc hwr hwc hwrows hwcols final hbd hbo hsd hso hwp htrace rfl
  have hchoice : ∀ (j : Fin P) (i : Fin (4 * 6)),
      choice (btGrowingOffsetRectangle
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff (finProdFinEquiv (j, i))) =
          decide (i.val < 2 * 6) := by
    intro j i
    exact fwBridgeSeedWideGrowthChoice_offset_restrict hrect hseedrect hwide hmax hoff hcap otherChoice j i
  have hseedFixed (i : Fin 16) (side : Bool) :
      entry grown (fwPhysicalSeedCell hseedrect hs choice i side) =
        entry final (fwPhysicalSeedCell hseedrect hs choice i side) := by
    apply hfixed
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(finProdFinEquiv (i, (0 : Fin (4 * 6))), prefixPairCorner (0 : Fin 2) side),
      Finset.mem_univ _, rfl⟩
  have hlabel : fwPhysicalSeedLabel hseedrect hs choice grown = fwPhysicalSeedLabel hseedrect hs choice final := by
    funext i
    apply Prod.ext
    · exact hseedFixed i false
    · exact hseedFixed i true
  have hgridGrown :
      (let valueGap : Sum (ℕ × ℕ) BTSelectedStage → ℕ := Sum.elim fwPhysicalSeedLabelGap BTSelectedStage.gap
       let base := Finset.univ.image (fun i => Sum.inl (fwPhysicalSeedLabel hseedrect hs choice grown i) :
         Fin 16 → Sum (ℕ × ℕ) BTSelectedStage)
       let labels : List (Sum (ℕ × ℕ) BTSelectedStage) := stages.map Sum.inr
       CompleteEvenGrid (base ∪ labels.toFinset) valueGap last) := by
    dsimp only
    rw [hlabel]
    exact hbounded.2.2.2.2.2.1
  refine ⟨p, hder, hexp, batches, hvalid, hdisjoint, hbudget, candidates, hcard, kept, hsub, hkept,
    hcand, hvariance, hinj, hav, rows, cols, hr, hc, sr, sc, hsr, hsc, wr, wc, hwr, hwc,
    blocks, hlen, final, gap, chosen, width, stock, last, extra, ?_, hbounded, hstage, ?_⟩
  · exact ⟨htrace, hoff, gr, gc, hgr, hgc, grown, hgrmap, hgcmap, hchoice, hgrpacked, hgcpacked,
      hgdisj, hends, hfixed, hgridGrown, hplaced, hdiagGap, hrowGap, hcolGap, hcomplete⟩
  · exact ⟨hrmap, hcmap, hsrmap, hscmap, hwrmap, hwcmap, hrows, hcols, hbrdisj,
      hsrows, hscols, hsdisj, ⟨hwrows, hwcols, hwdisj, hwrsafe, hwcsafe⟩,
      hseedEnds, hwideEnds, hbd, hbo, hsd, hso, hmatched, hpair, havoid, hwp, hbounds⟩

end
end Sude
