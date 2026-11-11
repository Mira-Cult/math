import Sude.DoubleBlockProtectedLogReallocation
import Sude.FWPhysicalDoubleBlockGaps

/-! Apply supplied FW packing and source placements to protected midpoint
reallocation; interval and proxy invoices remain explicit inputs. -/
namespace Sude
noncomputable section

theorem fw_double_block_family_separation {n P : ℕ}
    (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
 :
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc
    Function.Injective bridge ∧ Function.Injective wide ∧
      (∀ x y, bridge x ≠ wide y) ∧
      (∀ x y, bridge x ≠ seed y) ∧ (∀ x y, bridge x ≠ growth y) ∧
      (∀ x y, wide x ≠ seed y) ∧ (∀ x y, wide x ≠ growth y) := by
  dsimp only
  obtain ⟨hfamily, _⟩ := fw_four_family_pair_cells_injective hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
  change Function.Injective cells at hfamily
  have hb : Function.Injective (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n x)))) =
        cells (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n y)))) from h)
    exact (fwBlockPairIndex 5 n).injective (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj he)))
  have hw : Function.Injective (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n x))) =
        cells (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n y))) from h)
    exact (fwBlockPairIndex (3 * (n / 450)) n).injective (Sum.inr.inj (Sum.inl.inj he))
  have hbw : ∀ x y, fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x ≠
      fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc y := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n x)))) =
      cells (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n y))) from h)
    simp only [Sum.inl.injEq, reduceCtorEq] at he
  have hbs : ∀ x y, fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x ≠
      fwSeedExistingPairCells hseed hs choice sr sc hsr hsc y := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n x)))) =
      cells (Sum.inl (Sum.inl (Sum.inr y))) from h)
    simp only [Sum.inl.injEq, reduceCtorEq] at he
  have hbg : ∀ x y, fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x ≠
      btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc y := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n x)))) =
      cells (Sum.inr y) from h)
    simp only [reduceCtorEq] at he
  have hws : ∀ x y, fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x ≠
      fwSeedExistingPairCells hseed hs choice sr sc hsr hsc y := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n x))) =
      cells (Sum.inl (Sum.inl (Sum.inr y))) from h)
    simp only [Sum.inl.injEq, reduceCtorEq] at he
  have hwg : ∀ x y, fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x ≠
      btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc y := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n x))) =
      cells (Sum.inr y) from h)
    simp only [reduceCtorEq] at he
  exact ⟨hb, hw, hbw, hbs, hbg, hws, hwg⟩


/-- Under supplied normalized FW packing and source placements, choose and
install bridge and wide block controls on one square while preserving all
seed/growth cells. The source intervals and positive proxy invoices remain
explicit; no grid or full-line conclusion is claimed. -/
theorem fw_protected_double_block_log_reallocation {n P m N : ℕ}
    (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
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
    (low high : Fin N → Finset ℕ) (hmatched : ∀ block ∈ blocks, block.MatchedValid low high)
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
        Real.sqrt (Vw * Real.log (4 * (m : ℝ)) / 2)) := by
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
    low high hmatched old hplaced
  obtain ⟨πb, sb, πw, sw, new, hbe, hwe, hsf, hgf, hfix, hbi, hwi, hbgaps, hwgaps,
    hbgap, hwgap, hscoreb, hscorew⟩ :=
      double_block_two_family_protected_log_reallocation hB hm old _ _ _ _ hb hw hbw hbs hbg hws hwg
        line lob hib loww hiw Vb Vw hVb hVw hintervalb hintervalw hinvoiceb hinvoicew gapb gapw hgapb hgapw
  exact ⟨πb, sb, πw, sw, new, hbe, hwe, hsf, hgf, hfix, hbi, hwi, hbgaps, hwgaps,
    hbgap, hwgap, (fun j b => hposw j (πw j b)), hscoreb, hscorew⟩

end
end Sude
