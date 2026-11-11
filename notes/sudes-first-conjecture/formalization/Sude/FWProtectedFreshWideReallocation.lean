import Sude.FWProtectedDoubleBlockLogReallocation
import Sude.FWFreshWidePhysicalCenteredSelection

/-! A fresh bridge and wide reallocation retains the existing protected
fields and controls a centered wide contrast. Spare and midpoint contrasts,
previous witnesses, and prime targets are separate obligations. -/
namespace Sude
noncomputable section

theorem fw_protected_double_block_fresh_wide_reallocation {n P m : ℕ}
    (hn : 450 ≤ n) (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (other : Fin (fwJointRectangleCount n 254) → Bool)
    (hchoice : choice = fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff other)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (old : Cell n ≃ Fin (n * n))
    (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (hdiag : ∀ t side, entry old (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hord : ∀ x, entry old (fwBridgeLayerCells br bc hbr hbc x) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x))
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (μ X : ℝ) (hX : (100 : ℝ) ≤ X)
    (hmlo : (243/500 : ℝ)*X ≤ μ) (hmhi : μ ≤ (123/250 : ℝ)*X)
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ X) (fwReflectedRight μ X))
      (bmorHighBins (fwReflectedLeft μ X) (fwReflectedRight μ X)))
    (hplaced : ∀ x : FWWideInputs n, entry old (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (hm : 0 < m) (line : Fin m → Cell n → Prop)
    (lob hib : Fin 5 → ℝ) (loww hiw : Fin (3 * (n / 450)) → ℝ)
    (Vb Vw : ℝ) (hVb : 0 < Vb) (hVw : 0 < Vw)
    (hintervalb : ∀ j b p, doubleBlockPairMidpoint
      (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) old j b p ∈ Set.Icc (lob j) (hib j))
    (hintervalw : ∀ j b p, doubleBlockPairMidpoint
      (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) old j b p ∈ Set.Icc (loww j) (hiw j))
    (hinvoiceb : ∀ l, doubleBlockCombinedProxy
      (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) (line l) lob hib ≤ Vb / 4)
    (hinvoicew : ∀ l, doubleBlockCombinedProxy
      (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) (line l) loww hiw ≤ Vw / 4) :
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc
    let gapb := fun j b => (fwBridgeStageBlock n initial batches hvalid j b).high₁ -
      (fwBridgeStageBlock n initial batches hvalid j b).low₁
    let gapw := fun j b =>
      let block := blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,b)))
      block.high₁ - block.low₁
    ∃ (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8)))) (sb : (Fin 5 × Fin (3 * (n + 8))) → Bool)
      (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
      (sw : (Fin (3 * (n / 450)) × Fin (3 * (n + 8))) → Bool)
      (new : Cell n ≃ Fin (n * n)),
      (∀ j b p side, entry new (bridge ((j,b,p),side)) =
        entry old (bridge ((j,πb j b,doubleBlockPairSwap (sb (j,b)) p),side))) ∧
      (∀ j b p side, entry new (wide ((j,b,p),side)) =
        entry old (wide ((j,πw j b,doubleBlockPairSwap (sw (j,b)) p),side))) ∧
      (∀ x, entry new (seed x) = entry old (seed x)) ∧
      (∀ x, entry new (growth x) = entry old (growth x)) ∧
      (∀ c, c ∉ Set.range bridge → c ∉ Set.range wide → entry new c = entry old c) ∧
      (∀ j, Finset.univ.image (fun x : (Fin (3 * (n + 8)) × Fin 2) × Bool =>
        entry new (bridge ((j,x.1.1,x.1.2),x.2))) =
        Finset.univ.image (fun x : (Fin (3 * (n + 8)) × Fin 2) × Bool =>
        entry old (bridge ((j,x.1.1,x.1.2),x.2)))) ∧
      (∀ j, Finset.univ.image (fun x : (Fin (3 * (n + 8)) × Fin 2) × Bool =>
        entry new (wide ((j,x.1.1,x.1.2),x.2))) =
        Finset.univ.image (fun x : (Fin (3 * (n + 8)) × Fin 2) × Bool =>
        entry old (wide ((j,x.1.1,x.1.2),x.2)))) ∧
      (∀ gap : Fin 5 → Fin (3 * (n + 8)) → ℕ, (∀ j b p,
        entry old (bridge ((j,b,p),true)) = entry old (bridge ((j,b,p),false)) + gap j b) →
        ∀ j b p, entry new (bridge ((j,b,p),true)) =
          entry new (bridge ((j,b,p),false)) + gap j (πb j b)) ∧
      (∀ gap : Fin (3 * (n / 450)) → Fin (3 * (n + 8)) → ℕ, (∀ j b p,
        entry old (wide ((j,b,p),true)) = entry old (wide ((j,b,p),false)) + gap j b) →
        ∀ j b p, entry new (wide ((j,b,p),true)) =
          entry new (wide ((j,b,p),false)) + gap j (πw j b)) ∧
      (∀ j b p, entry new (bridge ((j,b,p),true)) =
        entry new (bridge ((j,b,p),false)) + gapb j (πb j b)) ∧
      (∀ j b p, entry new (wide ((j,b,p),true)) =
        entry new (wide ((j,b,p),false)) + gapw j (πw j b)) ∧
      (∀ j b, 0 < gapw j (πw j b)) ∧
      (∀ l, |doubleBlockActualCenteredScore bridge (line l) old new| <
        Real.sqrt (Vb * Real.log (4 * (m : ℝ)) / 2)) ∧
      (∀ l, |doubleBlockActualCenteredScore wide (line l) old new| <
        Real.sqrt (Vw * Real.log (4 * (m : ℝ)) / 2)) ∧
      (∀ j side r, (if side = true then packedRectangleCorner hs choice
        (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0) ∈ mainCells n
        else packedRectangleCorner hs choice
        (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0) ∈ antiCells n)) ∧
      (∀ j side, (∑ r : Fin 12,
        ((entry new (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0)) : ℝ) -
         ((entry new (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0)) : ℝ) +
          (entry new (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),1)) : ℝ))/2)) =
        -(1/2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n side, (gapw j (πw j b) : ℝ)) ∧
      |(1/2 : ℝ) * ((∑ j, ∑ b ∈ fwWideSignedGapSlots n true, (gapw j (πw j b) : ℝ)) -
        ∑ j, ∑ b ∈ fwWideSignedGapSlots n false, (gapw j (πw j b) : ℝ))| <
        2 * Real.sqrt ((3/2 : ℝ) * ((3*(n/450) : ℕ) : ℝ) * ((64/235 : ℝ)*X)^2 * Real.log 16) := by
  classical
  dsimp only
  obtain ⟨hb, hw, hbw, hbs, hbg, hws, hwg⟩ := fw_double_block_family_separation
    hP hrect hseed hwide hoff hs choice br bc sr sc wr wc gr gc
    hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  have hB : 0 < 3 * (n + 8) := by omega
  let gapb := fun j b => (fwBridgeStageBlock n initial batches hvalid j b).high₁ -
    (fwBridgeStageBlock n initial batches hvalid j b).low₁
  let gapw := fun j b =>
    let block := blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,b)))
    block.high₁ - block.low₁
  have hgapb : ∀ j b p, entry old (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,b,p),true)) =
      entry old (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,b,p),false)) + gapb j b := by
    intro j b p
    exact fw_bridge_physical_double_common_gap hrect hs choice br bc hbr hbc initial batches hvalid old hdiag hord j b p
  have ⟨hposw, hgapw⟩ := fw_wide_physical_selected_double_gap hwide hs choice wr wc hwr hwc blocks hlen
    _ _ hmatched old hplaced
  obtain ⟨πb, sb, hscoreb⟩ := double_block_log_simultaneous_sample_exists hB hm Vb hVb
    _ line old lob hib hintervalb hinvoiceb
  obtain ⟨_, πw, sw, hscorew, hcontrast⟩ := fw_fresh_wide_midpoint_gap_selection hn hm hwide hs choice wr wc hwr hwc
    μ X hX hmlo hmhi blocks hlen hmatched old hplaced line Vw hVw loww hiw hintervalw hinvoicew
  obtain ⟨new, hbe, hwe, hsf, hgf, hfix, hbi, hwi, hbgaps, hwgaps⟩ :=
    fw_reallocate_two_double_families old _ _ _ _ hb hw hbw hbs hbg hws hwg
      πb (fun j b => doubleBlockPairSwap (sb (j,b)))
      πw (fun j b => doubleBlockPairSwap (sw (j,b)))
  have hbgap := hbgaps gapb hgapb
  have hwgap := hwgaps gapw hgapw
  have hgeom := fw_wide_balanced_physical_centered_gap hrect hseed hwide hoff hs other
    wr wc hwr hwc new πw (fun j b => (gapw j b : ℝ)) (by
      intro j b
      rw [← hchoice]
      exact_mod_cast hwgap j b 0)
  dsimp only at hgeom
  rw [← hchoice] at hgeom
  refine ⟨πb, sb, πw, sw, new, hbe, hwe, hsf, hgf, hfix, hbi, hwi, hbgaps, hwgaps,
    hbgap, hwgap, (fun j b => hposw j (πw j b)), ?_, ?_, hgeom.1, hgeom.2, ?_⟩
  · intro l
    rw [double_block_actual_centered_score_eq_sample _ (line l) old new πb sb hbe]
    exact hscoreb l
  · intro l
    rw [double_block_actual_centered_score_eq_sample _ (line l) old new πw sw hwe]
    exact hscorew l
  · simpa [gapw, fwPermutedWideSourceGap] using hcontrast

end
end Sude
