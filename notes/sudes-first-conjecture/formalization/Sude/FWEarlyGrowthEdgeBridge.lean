import Sude.FWPhysicalEdgeBridgeGrid
import Sude.FWPreservedWideEdgeRoles

/-! Retain the selected early and growth witnesses while adding per-edge
bridge coverage conditional on the actual crossing alternative. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- The existing early/growth witness yields a per-edge bridge grid if its
actual trace reaches `X/23`. The stage-cap alternative is kept separately and
does not imply crossing. This does not assert switch separation. -/
theorem bmor_fw_early_growth_edge_bridge
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
    ∃ p : Fin 3 → Equiv.Perm (Fin n),
      (∀ i v, p i v ≠ v) ∧
      (∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
        500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card) ∧
    ∃ (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j),
    ∃ (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
      (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16),
      candidates ⊆ seeds ∧
      (∀ x, sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard x ∈
        poolFinset n \ priorBridgeReservation ∅ (Finset.range 5) batches) ∧
    ∃ (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
      (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
      (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
      (hwc : wc.length = (3 * (n / 450)) * 3)
      (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
      (old : Cell n ≃ Fin (n*n)) (gap : ℕ) (chosen : Finset ℕ) (width : ℝ)
      (stock : Finset ℕ) (last : ℕ) (extra : List BTSelectedStage),
    let stages := [⟨gap, chosen, width⟩] ++ extra
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    let offset := 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)
    ∃ (_trace : BTGrowingTrace 2 (6 * (n + 8)) initial 32 stock last stages)
      (hoff : offset + stages.length * (4 * 6) ≤ fwJointRectangleCount n 254)
      (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3)
      (hgc : gc.length = stages.length * 3) (grown : Cell n ≃ Fin (n*n)),
      stages.length ≤ 238 ∧
      ((poolMaximum n : ℝ) / 23 ≤ last ∨ stages.length = 238) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) stages ∧
      (∀ c ∈ fwGrowthEarlyRoleCells hrect hseedrect hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
        entry grown c = entry old c) ∧
      rows.map Prod.fst = bridgeRepeatedPermutations 5 p ∧
      cols.map Prod.fst = bridgeRepeatedPermutations 5 p ∧
      sr.map Prod.fst = bridgeRepeatedPermutations 16 p ∧
      sc.map Prod.fst = bridgeRepeatedPermutations 16 p ∧
      gr.map Prod.fst = bridgeRepeatedPermutations stages.length p ∧
      gc.map Prod.fst = bridgeRepeatedPermutations stages.length p ∧
      (∀ x, entry old (fwSeedOrdinaryCells sr sc hsr hsc x) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x))) ∧
      (∀ x, entry old (fwBridgeLayerCells rows cols hr hc x) =
        fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x)) ∧
      (∀ (i : Fin (stages.length * 3)) (e : Fin n),
        entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, true))))) =
        entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, false))))) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e) ∧
      (∀ (i : Fin (stages.length * 3)) (e : Fin n),
        entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, true))))) =
        entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, false))))) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e) ∧
      (∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n),
        ∃ wideGap : ℕ, 0 < wideGap ∧ wideGap % 2 = 0 ∧
          (∀ network : Bool,
            entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e network true)) =
            entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e network false)) + wideGap) ∧
          (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (wideGap : ℝ) ∧ (wideGap : ℝ) < poolMaximum n) ∧
      (∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) (side : Bool),
        fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e false side) =
          ((if side then p k e else e), (wr.get (bridgeStageLayerIndex hwr j k)).2 e) ∧
        fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e true side) =
          ((wc.get (bridgeStageLayerIndex hwc j k)).2 e, (if side then p k e else e))) ∧
      ((poolMaximum n : ℝ) / 23 ≤ last →
        ∀ (edge : Fin 3 × Fin n) (network : Bool),
        let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
        let radius := last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j
        let initialGap := fwPhysicalEdgeTraceGap grown (fwSeedEdgeCells sr sc hsr hsc edge network)
          (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network)
        CompleteEvenGrid
          ((Finset.univ : Finset (Sum (Fin 16) (Fin stages.length))).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
            (Finset.range 5).image (Sum.inr : ℕ → Sum (Sum (Fin 16) (Fin stages.length)) ℕ))
          (joinedBridgeGap initialGap batches index) radius ∧
        (poolMaximum n : ℝ) ≤ radius ∧
        (∀ j : Fin 5, entry grown (fwBridgeLayerCells rows cols hr hc ((j, edge), (network, true))) =
          entry grown (fwBridgeLayerCells rows cols hr hc ((j, edge), (network, false))) +
            selectedBridgeGap batches index j)) := by
  dsimp only
  obtain ⟨p, hder, hexp, batches, hvalid, hdisjoint, hbudget, candidates, hcard,
    kept, hsub, hkept, hcand, hvariance, hinj, hav, rows, cols, hr, hc,
    sr, sc, hsr, hsc, wr, wc, hwr, hwc, blocks, hlen, old, gap, chosen, width,
    stock, last, extra, hinstall, hbounded, hstage, hrest⟩ :=
    bmor_fw_early_and_growth_physical piFour bmor upper lower sharp upperSharp n hnlo hnhi
      otherChoice a seeds hseed hprime hcount
  obtain ⟨trace, hoff, gr, gc, hgr, hgc, grown, hgrmap, hgcmap, hchoice, hgrpacked, hgcpacked,
    hgdisj, hends, hfixed, hgrid, hplaced, hdiagGap, hrow, hcol, hcomplete⟩ := hinstall
  obtain ⟨hrmap, hcmap, hsrmap, hscmap, hwrmap, hwcmap, hrows, hcols, hbrdisj,
    hsrows, hscols, hsdisj, hwpack, hseedEnds, hwideEnds, hbd, hbo, hsd, hso,
    hmatched, hpair, havoid, hwp, hbounds⟩ := hrest
  refine ⟨p, hder, hexp, batches, hvalid, candidates, hcard, kept, hsub, hkept, hcand, hav,
    rows, cols, hr, hc, sr, sc, hsr, hsc, wr, wc, hwr, hwc, blocks, hlen, old,
    gap, chosen, width, stock, last, extra, trace, hoff, gr, gc, hgr, hgc, grown,
    hbounded.2.1, hbounded.2.2.1, hbounded.2.2.2.2.1, hfixed,
    hrmap, hcmap, hsrmap, hscmap, hgrmap, hgcmap, hso, hbo, hrow, hcol, ?_, ?_, ?_⟩
  · intro j k e
    exact fw_preserved_wide_edge_physical_gap blocks hlen _ _ _ _ _ rows cols hr hc
      sr sc hsr hsc wr wc hwr hwc old grown hfixed hbounds.2 j k e
  · intro j k e side
    exact fw_wide_edge_physical_coordinates _ _ _ wr wc hwr hwc p hwideEnds j k e side
  · intro hcross
    have hresult := fw_physical_edge_bridge_witness_grid p batches hvalid candidates hcard kept hsub hkept hav
      _ _ _ _ _ rows cols hr hc hrmap hcmap sr sc hsr hsc hsrmap hscmap wr wc hwr hwc old grown
      hfixed hso hbo trace hcross _ hoff gr gc hgr hgc hgrmap hgcmap hrow hcol
    exact hresult.1

end
end Sude
