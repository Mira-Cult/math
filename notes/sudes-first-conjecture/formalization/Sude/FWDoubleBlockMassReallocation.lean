import Sude.FWProtectedDoubleBlockLogReallocation
import Sude.FWDoubleBlockSourceIntervals
import Sude.DoubleBlockProxyInvoice

/-! Conditional FW midpoint allocation from supplied squared pair-incidence
bounds. No geometric incidence estimate, theta witness, grid, or full-line
claim is asserted. -/
namespace Sude
noncomputable section

theorem fw_protected_double_block_mass_reallocation {n P m : ℕ}
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
    (hm : 0 < m) (line : Fin m → Cell n → Prop)
    (Mb Mw Vb Vw : ℝ) (hMb : 0 ≤ Mb) (hMw : 0 ≤ Mw) (hVb : 0 < Vb) (hVw : 0 < Vw)
    (hmassb : ∀ l, (∑ j : Fin 5, ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) (line l) (j,b,p)) ^ 2) ≤ Mb)
    (hmassw : ∀ l, (∑ j : Fin (3 * (n / 450)), ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) (line l) (j,b,p)) ^ 2) ≤ Mw)
    (hinvoiceb : 2 * ((23 / 924 : ℝ) * poolMaximum n) ^ 2 * Mb ≤ Vb)
    (hinvoicew : 2 * (2 * (poolMaximum n : ℝ) / 235) ^ 2 * Mw ≤ Vw) :
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
  let lob : Fin 5 → ℝ := fun _ => (poolMaximum n : ℝ) / 2 - (23 / 1848 : ℝ) * poolMaximum n
  let hib : Fin 5 → ℝ := fun _ => (poolMaximum n : ℝ) / 2 + (23 / 1848 : ℝ) * poolMaximum n
  let loww : Fin (3 * (n / 450)) → ℝ := fun _ => μ - (poolMaximum n : ℝ) / 235
  let hiw : Fin (3 * (n / 450)) → ℝ := fun _ => μ + (poolMaximum n : ℝ) / 235
  have hIb : ∀ j b p, doubleBlockPairMidpoint
      (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) old j b p ∈ Set.Icc (lob j) (hib j) := by
    intro j b p
    exact fw_bridge_double_block_source_interval hrect hs choice br bc hbr hbc initial batches hvalid old hdiag hord j b p
  have hIw : ∀ j b p, doubleBlockPairMidpoint
      (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) old j b p ∈ Set.Icc (loww j) (hiw j) := by
    intro j b p
    exact fw_wide_double_block_source_interval hwide hs choice wr wc hwr hwc blocks hlen old hplaced
      μ (poolMaximum n) hX hmlo hmhi hmatched j b p
  have hPb : ∀ l, doubleBlockCombinedProxy
      (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) (line l) lob hib ≤ Vb / 4 := by
    intro l
    have h := double_block_proxy_uniform_pair_invoice
      (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) (line l) lob hib
      (by intro j; dsimp [lob, hib]; linarith)
      ((23 / 924 : ℝ) * poolMaximum n) Mb (by positivity) hMb
      (by intro j; dsimp [lob, hib]; ring_nf; linarith) (hmassb l)
    linarith [h.2]
  have hPw : ∀ l, doubleBlockCombinedProxy
      (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) (line l) loww hiw ≤ Vw / 4 := by
    intro l
    have h := double_block_proxy_uniform_pair_invoice
      (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) (line l) loww hiw
      (by intro j; dsimp [loww, hiw]; linarith)
      (2 * (poolMaximum n : ℝ) / 235) Mw (by positivity) hMw
      (by intro j; dsimp [loww, hiw]; ring_nf; linarith) (hmassw l)
    linarith [h.2]
  exact fw_protected_double_block_log_reallocation hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols old
    initial batches hvalid hdiag hord blocks hlen
    (bmorLowBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n)))
    (bmorHighBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n)))
    hmatched hplaced hm line lob hib loww hiw Vb Vw hVb hVw hIb hIw hPb hPw

end
end Sude
