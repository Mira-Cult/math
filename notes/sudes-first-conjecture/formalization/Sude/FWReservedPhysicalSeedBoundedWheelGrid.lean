import Sude.FWReservedEarlyPlacementFirstWheel
import Sude.FWWheelFirstBandActualStep
import Sude.FWPhysicalSeedWitnessTraceGrid

/-! Combine the actual early square and its first wheel stage with a bounded
abstract continuation and an actual physical-seed-value-labeled even grid.
No physical installation of growth stages or guaranteed crossing is claimed. -/
namespace Sude
noncomputable section
local instance fwReservedPhysicalSeedStageDecidable : DecidableEq BTSelectedStage := Classical.decEq _
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- The continued first-wheel trace retains the same early witnesses and the
first selected stage, and stops at X/23 or the explicit stage cap. -/
theorem bmor_fw_reserved_early_physical_seed_bounded_wheel_grid
    (piFour : BMORFinitePiFour) (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n P₀ : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (hPmin : 16 ≤ P₀) (hPmax : P₀ ≤ 270)
    (otherChoice : Fin (fwJointRectangleCount n P₀) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    let hrect := (fw_reserved_wide_rectangle_capacity hnlo hPmin hPmax).1
    let hseedrect := (fw_reserved_wide_rectangle_capacity hnlo hPmin hPmax).2.1
    let hwide := (fw_reserved_wide_rectangle_capacity hnlo hPmin hPmax).2.2.1
    let hs := (fw_reserved_wide_rectangle_capacity hnlo hPmin hPmax).2.2.2
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
      (final : Cell n ≃ Fin (n*n)) (gap : ℕ) (chosen : Finset ℕ) (width : ℝ)
      (stock : Finset ℕ) (last : ℕ) (extra : List BTSelectedStage),
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
  obtain ⟨p, hder, hexp, batches, hvalid, hdisjoint, hbudget, candidates, hcard,
    kept, hsub, hkept, hcand, hvariance, hinj, hav, rows, cols, hr, hc,
    sr, sc, hsr, hsc, wr, wc, hwr, hwc, blocks, hlen, final, gap, chosen, width,
    hstage, hrest⟩ :=
    bmor_fw_reserved_early_placement_first_wheel piFour bmor upper lower sharp upperSharp n P₀
      hnlo hnhi hPmin hPmax otherChoice a seeds hseed hprime hcount
  let hrect := (fw_reserved_wide_rectangle_capacity hnlo hPmin hPmax).1
  let hseedrect := (fw_reserved_wide_rectangle_capacity hnlo hPmin hPmax).2.1
  let hwide := (fw_reserved_wide_rectangle_capacity hnlo hPmin hPmax).2.2.1
  let hs := (fw_reserved_wide_rectangle_capacity hnlo hPmin hPmax).2.2.2
  let choice := fwBridgeSeedRectangleChoice hrect hseedrect (fwWideRectangleChoice hwide otherChoice)
  let initial := ((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
  have hsd : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      entry final (packedRectangleCorner hs choice (fwSeedRectangle hseedrect x.1, x.2)) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept
            (prefixRectangleInput (by omega) x)) := by
    rcases hrest with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsd, _⟩
    exact hsd
  have hfirst : BTGrowingTrace 2 (6 * (n + 8)) initial 32
      (initial \ pairFootprint chosen gap) (32 + gap) [⟨gap, chosen, width⟩] := by
    rcases hstage with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htrace⟩
    exact htrace
  obtain ⟨stock, last, extra, htrace, hcap, hstop, hnarrow⟩ :=
    fw_first_band_trace_first_window_bounded_stop piFour lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hlen (32 + gap)
      (initial \ pairFootprint chosen gap) [⟨gap, chosen, width⟩] hfirst (by simp)
  have hmid : ∀ p ∈ chosen, ∀ q ∈ chosen,
      |(((p : ℝ) + (p + gap : ℕ)) / 2) - (((q : ℝ) + (q + gap : ℕ)) / 2)| <
        (poolMaximum n : ℝ) / 6 := by
    rcases hstage with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hmid, _, _⟩
    exact hmid
  have hnarrowAll : NarrowedStages ((poolMaximum n : ℝ) / 6)
      ([⟨gap, chosen, width⟩] ++ extra) := by
    intro stage hmem p hp q hq
    have hs' : stage = ⟨gap, chosen, width⟩ ∨ stage ∈ extra := by simpa using hmem
    rcases hs' with rfl | hs'
    · exact hmid p hp q hq
    · exact hnarrow stage hs' p hp q hq
  have hgrid := fw_physical_seed_witness_trace_grid batches candidates hcard kept hsub hkept hinj hav
      blocks hseedrect hs choice final hsd htrace
  exact ⟨p, hder, hexp, batches, hvalid, hdisjoint, hbudget, candidates, hcard,
    kept, hsub, hkept, hcand, hvariance, hinj, hav, rows, cols, hr, hc,
    sr, sc, hsr, hsc, wr, wc, hwr, hwc, blocks, hlen, final, gap, chosen, width,
    stock, last, extra, ⟨htrace, hcap, hstop, hnarrow, hnarrowAll, hgrid⟩, hstage, hrest⟩

end
end Sude
