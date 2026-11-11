import Sude.FWDoubleBlockMassReallocation
import Sude.FWGroupedRowColumnMass
import Sude.PhysicalAllLineWeights

/-! One shared FW bridge/wide midpoint allocation for all labelled lines.
Diagonal squared-incidence hypotheses are supplied, not established. -/
namespace Sude
noncomputable section

/-- Conditional all-line bridge and wide incidence mass adapter. -/
theorem fw_joint_all_line_grouped_mass_of_diagonals {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers reservedCols (((bc ++ sc) ++ wc) ++ gc))
    (hbm : (∑ j : Fin 5, ∑ b : Fin (3*(n+8)), ∑ p : Fin 2,
       (physicalPairLineWeight (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
         (fun z => z ∈ mainCells n) (j,b,p))^2) ≤ 94)
    (hba : (∑ j : Fin 5, ∑ b : Fin (3*(n+8)), ∑ p : Fin 2,
       (physicalPairLineWeight (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
         (fun z => z ∈ antiCells n) (j,b,p))^2) ≤ 94)
    (hwm : (∑ j : Fin (3*(n/450)), ∑ b : Fin (3*(n+8)), ∑ p : Fin 2,
       (physicalPairLineWeight (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
         (fun z => z ∈ mainCells n) (j,b,p))^2) ≤ (18:ℝ)*((3*(n/450):ℕ):ℝ)+4)
    (hwa : (∑ j : Fin (3*(n/450)), ∑ b : Fin (3*(n+8)), ∑ p : Fin 2,
       (physicalPairLineWeight (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
         (fun z => z ∈ antiCells n) (j,b,p))^2) ≤ (18:ℝ)*((3*(n/450):ℕ):ℝ)+4) :
    (∀ l : Fin ((n+n)+2), (∑ j : Fin 5, ∑ b : Fin (3*(n+8)), ∑ p : Fin 2,
       (physicalPairLineWeight (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
         (fun z => z ∈ physicalAllLineCells l) (j,b,p))^2) ≤ 94) ∧
    (∀ l : Fin ((n+n)+2), (∑ j : Fin (3*(n/450)), ∑ b : Fin (3*(n+8)), ∑ p : Fin 2,
       (physicalPairLineWeight (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
         (fun z => z ∈ physicalAllLineCells l) (j,b,p))^2) ≤ (18:ℝ)*((3*(n/450):ℕ):ℝ)+4) := by
  classical
  obtain ⟨hbrrow,hbrcol,hwrow,hwcol⟩ := fw_joint_bridge_wide_grouped_row_column_mass
    hrect hwide hs choice br bc sr sc wr wc gr gc hbr hbc hwr hwc reservedRows reservedCols hrows hcols
  constructor <;> intro l
  all_goals
    cases hl : (finSumFinEquiv (m := n+n) (n := 2)).symm l with
    | inl rc =>
      cases hrc : (finSumFinEquiv (m := n) (n := n)).symm rc with
      | inl r => first | simpa only [physicalAllLineCells, hl, hrc, mem_rowCells] using hbrrow r | simpa only [physicalAllLineCells, hl, hrc, mem_rowCells] using hwrow r
      | inr c => first | simpa only [physicalAllLineCells, hl, hrc, mem_columnCells] using hbrcol c | simpa only [physicalAllLineCells, hl, hrc, mem_columnCells] using hwcol c
    | inr diag =>
      by_cases hzero : diag = 0
      · first | simpa only [physicalAllLineCells, hl, hzero, if_true] using hbm | simpa only [physicalAllLineCells, hl, hzero, if_true] using hwm
      · first | simpa only [physicalAllLineCells, hl, hzero, if_false] using hba | simpa only [physicalAllLineCells, hl, hzero, if_false] using hwa


/-- From one supplied source square and joint packing, select and realize one
bridge/wide allocation meeting all labelled midpoint bounds. The four
same-choice diagonal mass bounds, source validity, positive invoices, and
all placement hypotheses remain explicit. No grid or full-line bound follows. -/
theorem fw_all_line_protected_double_block_reallocation {n P : ℕ}
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
    (μ : ℝ) (hX : (100 : ℝ) ≤ poolMaximum n)
    (hmlo : (243 / 500 : ℝ) * poolMaximum n ≤ μ)
    (hmhi : μ ≤ (123 / 250 : ℝ) * poolMaximum n)
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n))))
    (hplaced : ∀ x : FWWideInputs n, entry old (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (Vb Vw : ℝ) (hVb : 0 < Vb) (hVw : 0 < Vw)
    (hbridgeMain : (∑ j : Fin 5, ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
        (fun c => c ∈ mainCells n) (j,b,p)) ^ 2) ≤ 94)
    (hbridgeAnti : (∑ j : Fin 5, ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
        (fun c => c ∈ antiCells n) (j,b,p)) ^ 2) ≤ 94)
    (hwideMain : (∑ j : Fin (3 * (n / 450)), ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
        (fun c => c ∈ mainCells n) (j,b,p)) ^ 2) ≤ (18 : ℝ) * ((3 * (n / 450) : ℕ) : ℝ) + 4)
    (hwideAnti : (∑ j : Fin (3 * (n / 450)), ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
        (fun c => c ∈ antiCells n) (j,b,p)) ^ 2) ≤ (18 : ℝ) * ((3 * (n / 450) : ℕ) : ℝ) + 4)
    (hinvoiceb : 2 * ((23 / 924 : ℝ) * poolMaximum n) ^ 2 * 94 ≤ Vb)
    (hinvoicew : 2 * (2 * (poolMaximum n : ℝ) / 235) ^ 2 *
      ((18 : ℝ) * ((3 * (n / 450) : ℕ) : ℝ) + 4) ≤ Vw) :
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
      (∀ l, |doubleBlockActualCenteredScore bridge (fun c => c ∈ physicalAllLineCells l) old new| <
        Real.sqrt (Vb * Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) / 2)) ∧
      (∀ l, |doubleBlockActualCenteredScore wide (fun c => c ∈ physicalAllLineCells l) old new| <
        Real.sqrt (Vw * Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) / 2)) := by
  classical
  obtain ⟨hmassb, hmassw⟩ := fw_joint_all_line_grouped_mass_of_diagonals
    hrect hwide hs choice br bc sr sc wr wc gr gc hbr hbc hwr hwc
    (packedRectangleSupport hs choice)
    (LayerPacking.transposeCells (packedRectangleSupport hs choice ∪
      LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) hrows hcols
    hbridgeMain hbridgeAnti hwideMain hwideAnti
  exact fw_protected_double_block_mass_reallocation hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols old
    initial batches hvalid hdiag hord blocks hlen μ hX hmlo hmhi hmatched hplaced
    (by omega : 0 < (n + n) + 2) (fun l c => c ∈ physicalAllLineCells l)
    94 ((18 : ℝ) * ((3 * (n / 450) : ℕ) : ℝ) + 4) Vb Vw
    (by norm_num) (by positivity) hVb hVw hmassb hmassw hinvoiceb hinvoicew

end
end Sude
