import Sude.FWBalancedAllLineReallocation
import Sude.FWProtectedFreshWideMassReallocation

/-! Fresh balanced all-line midpoint selection with same-square centered wide
identities. Spare values and rectangle midpoint contrast remain separate. -/
namespace Sude
noncomputable section

theorem fw_balanced_all_line_fresh_wide_reallocation {n P : ℕ}
    (hn : 450 ≤ n) (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs (fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff otherChoice)) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs (fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff otherChoice) ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (old : Cell n ≃ Fin (n * n))
    (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (hdiag : ∀ t side, entry old (packedRectangleCorner hs (fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff otherChoice) (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hord : ∀ x, entry old (fwBridgeLayerCells br bc hbr hbc x) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x))
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (μ : ℝ) (hX : (100 : ℝ) ≤ poolMaximum n)
    (hmlo : (243 / 500 : ℝ) * poolMaximum n ≤ μ)
    (hmhi : μ ≤ (123 / 250 : ℝ) * poolMaximum n)
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n))))
    (hplaced : ∀ x : FWWideInputs n, entry old (fwWidePhysicalCells hwide hs (fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff otherChoice) wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
 :
    let bridge := fwBridgePhysicalDoubleCells hrect hs (fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff otherChoice) br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs (fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff otherChoice) wr wc hwr hwc
    let seed := fwSeedExistingPairCells hseed hs (fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff otherChoice) sr sc hsr hsc
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs (fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff otherChoice) gr gc hgr hgc
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
      (∀ l, |doubleBlockActualCenteredScore bridge (fun c => c ∈ physicalAllLineCells l) old new| <
        (poolMaximum n : ℝ) * (23 / 924 : ℝ) * Real.sqrt (94 * Real.log (8 * (n : ℝ) + 8))) ∧
      (∀ l, |doubleBlockActualCenteredScore wide (fun c => c ∈ physicalAllLineCells l) old new| <
        (poolMaximum n : ℝ) * (2 / 235 : ℝ) *
          Real.sqrt ((54 * ((n / 450 : ℕ) : ℝ) + 4) * Real.log (8 * (n : ℝ) + 8))) ∧
      (∀ j side r, (if side = true then packedRectangleCorner hs (fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff otherChoice)
        (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0) ∈ mainCells n
        else packedRectangleCorner hs (fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff otherChoice)
        (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0) ∈ antiCells n)) ∧
      (∀ j side, (∑ r : Fin 12,
        ((entry new (packedRectangleCorner hs (fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff otherChoice)
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0)) : ℝ) -
         ((entry new (packedRectangleCorner hs (fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff otherChoice)
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0)) : ℝ) +
          (entry new (packedRectangleCorner hs (fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff otherChoice)
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),1)) : ℝ))/2)) =
        -(1/2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n side, (gapw j (πw j b) : ℝ)) ∧
      |(1/2 : ℝ) * ((∑ j, ∑ b ∈ fwWideSignedGapSlots n true, (gapw j (πw j b) : ℝ)) -
        ∑ j, ∑ b ∈ fwWideSignedGapSlots n false, (gapw j (πw j b) : ℝ))| <
        2 * Real.sqrt ((3/2 : ℝ) * ((3*(n/450) : ℕ) : ℝ) * ((64/235 : ℝ)*(poolMaximum n : ℝ))^2 * Real.log 16) := by
  classical
  let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff otherChoice
  have hL : 3 ≤ fwJointRectangleCount n 254 := by omega
  have hd := fw_joint_bridge_wide_grouped_diagonal_mass hrect hseed hwide hoff hs hL otherChoice
    br bc sr sc wr wc gr gc hbr hbc hwr hwc
    (packedRectangleSupport hs choice)
    (LayerPacking.transposeCells (packedRectangleSupport hs choice ∪
      LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) hrows hcols
  dsimp only at hd
  obtain ⟨hbm, hba, hwm, hwa⟩ := hd
  have hJ : (0 : ℝ) ≤ ((3 * (n / 450) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hbridgeMain : (∑ j : Fin 5, ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
        (fun c => c ∈ mainCells n) (j,b,p)) ^ 2) ≤ 94 := by linarith [hbm]
  have hbridgeAnti : (∑ j : Fin 5, ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
        (fun c => c ∈ antiCells n) (j,b,p)) ^ 2) ≤ 94 := by linarith [hba]
  have hwideMain : (∑ j : Fin (3 * (n / 450)), ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
        (fun c => c ∈ mainCells n) (j,b,p)) ^ 2) ≤ (18 : ℝ) * ((3 * (n / 450) : ℕ) : ℝ) + 4 := by linarith [hwm]
  have hwideAnti : (∑ j : Fin (3 * (n / 450)), ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
        (fun c => c ∈ antiCells n) (j,b,p)) ^ 2) ≤ (18 : ℝ) * ((3 * (n / 450) : ℕ) : ℝ) + 4 := by linarith [hwa]
  obtain ⟨hmassb, hmassw⟩ := fw_joint_all_line_grouped_mass_of_diagonals
    hrect hwide hs choice br bc sr sc wr wc gr gc hbr hbc hwr hwc
    (packedRectangleSupport hs choice)
    (LayerPacking.transposeCells (packedRectangleSupport hs choice ∪
      LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) hrows hcols
    hbridgeMain hbridgeAnti hwideMain hwideAnti
  have hXpos : 0 < (poolMaximum n : ℝ) := by linarith
  have hXnonneg : 0 ≤ (poolMaximum n : ℝ) := le_of_lt hXpos
  have ⟨hVb, hVw⟩ := fw_double_block_scalar_invoices_pos n (poolMaximum n) hXpos
  have ⟨hIb, hIw⟩ := fw_double_block_scalar_invoice_equalities n (poolMaximum n)
  have h := fw_protected_double_block_fresh_wide_mass_reallocation hn hP hrect hseed hwide hoff hs choice otherChoice rfl
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols old
    initial batches hvalid hdiag hord blocks hlen μ hX hmlo hmhi hmatched hplaced
    (by omega : 0 < (n + n) + 2) (fun l c => c ∈ physicalAllLineCells l)
    94 ((18 : ℝ) * ((3 * (n / 450) : ℕ) : ℝ) + 4)
    (fwBridgeMidpointInvoice (poolMaximum n)) (fwWideMidpointInvoice n (poolMaximum n))
    (by norm_num) (by positivity) hVb hVw hmassb hmassw (le_of_eq hIb) (le_of_eq hIw)
  rw [fw_bridge_midpoint_invoice_threshold n (poolMaximum n) hXnonneg,
    fw_wide_midpoint_invoice_threshold n (poolMaximum n) hXnonneg] at h
  exact h

end
end Sude
