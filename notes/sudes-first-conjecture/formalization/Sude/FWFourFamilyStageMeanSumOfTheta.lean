import Sude.FWBridgeWideStageMeansOfTheta
import Sude.FWPhysicalPrefixMeanOfTheta
import Sude.ReservedPoolMean

/-! The same-square all-stage mean deviation bound. It uses only the generic
pool range for seed and growth stages and asserts no concentration, fresh
reference transport, witness existence, or full-line bound. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- The coarse physical mean bound holds for every four-family stage index. -/
theorem fw_four_stage_mean_coarse_of_theta {n P Q : ℕ}
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hQ : 0 < Q)
    (a : Cell n ≃ Fin (n * n))
    (cells : (FWFourStageIndex n P × Fin Q) × Bool → Cell n) :
    ∀ j : FWFourStageIndex n P,
      |(∑ i, ((entry a (cells ((j,i),false)) : ℝ) + entry a (cells ((j,i),true))) / 2) / (Q : ℝ) -
         centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
        (257 / 500 : ℝ) * (poolMaximum n : ℝ) := by
  intro j
  rw [prescribedPoolValues_mean]
  exact fw_physical_stage_mean_pool_bound_of_theta bmor lower upper hnlo hnhi hQ a
    (fun i side => cells ((j,i), side))

/-- Sum of four families whose individual terms have supplied absolute bounds. -/
theorem fw_four_family_sum_abs_bound {n P : ℕ}
    (X : ℝ) (f : FWFourStageIndex n P → ℝ)
    (hbridge : ∀ j : Fin 5, |f (Sum.inl (Sum.inl (Sum.inl j)))| ≤ (6109 / 231000 : ℝ) * X)
    (hseed : ∀ j : Fin 16, |f (Sum.inl (Sum.inl (Sum.inr j)))| ≤ (257 / 500 : ℝ) * X)
    (hwide : ∀ j : Fin (3 * (n / 450)), |f (Sum.inl (Sum.inr j))| ≤ X / 235)
    (hgrowth : ∀ j : Fin P, |f (Sum.inr j)| ≤ (257 / 500 : ℝ) * X) :
    |∑ j, f j| ≤
      ((5 : ℝ) * (6109 / 231000) + ((16 + P : ℕ) : ℝ) * (257 / 500) +
        ((3 * (n / 450) : ℕ) : ℝ) / 235) * X := by
  classical
  calc
    _ ≤ ∑ j, |f j| := Finset.abs_sum_le_sum_abs _ _
    _ = (∑ j : Fin 5, |f (Sum.inl (Sum.inl (Sum.inl j)))|) +
        (∑ j : Fin 16, |f (Sum.inl (Sum.inl (Sum.inr j)))|) +
        (∑ j : Fin (3 * (n / 450)), |f (Sum.inl (Sum.inr j))|) +
        ∑ j : Fin P, |f (Sum.inr j)| := by
      simp only [FWFourStageIndex, Fintype.sum_sum_type]
    _ ≤ (5 : ℝ) * ((6109 / 231000 : ℝ) * X) +
        16 * ((257 / 500 : ℝ) * X) +
        ((3 * (n / 450) : ℕ) : ℝ) * (X / 235) +
        (P : ℝ) * ((257 / 500 : ℝ) * X) := by
      gcongr
      · calc
          _ ≤ ∑ _j : Fin 5, (6109 / 231000 : ℝ) * X := Finset.sum_le_sum (by intro j _; exact hbridge j)
          _ = _ := by simp
      · calc
          _ ≤ ∑ _j : Fin 16, (257 / 500 : ℝ) * X := Finset.sum_le_sum (by intro j _; exact hseed j)
          _ = _ := by simp
      · calc
          _ ≤ ∑ _j : Fin (3 * (n / 450)), X / 235 := Finset.sum_le_sum (by intro j _; exact hwide j)
          _ = _ := by simp
      · calc
          _ ≤ ∑ _j : Fin P, (257 / 500 : ℝ) * X := Finset.sum_le_sum (by intro j _; exact hgrowth j)
          _ = _ := by simp
    _ = _ := by push_cast; ring

/-- The actual seed and growth stage means obey the pool-range bound, and
all four families together satisfy the displayed triangle bound. -/
theorem fw_four_family_stage_mean_sum_bound_of_theta
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n P L : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (_hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (a : Cell n ≃ Fin (n * n))
    (hdiag : ∀ t side, entry a (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hord : ∀ x, entry a (fwBridgeLayerCells br bc hbr hbc x) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x))
    (hplaced : ∀ x : FWWideInputs n, entry a (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n)))) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let means := fun j : FWFourStageIndex n P =>
      (∑ i, (((entry a (cells ((j, i), false)) : ℝ) + entry a (cells ((j, i), true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ)
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    (∀ j : Fin 16, |means (Sum.inl (Sum.inl (Sum.inr j))) - μ| ≤
      (257 / 500 : ℝ) * (poolMaximum n : ℝ)) ∧
    (∀ j : Fin P, |means (Sum.inr j) - μ| ≤
      (257 / 500 : ℝ) * (poolMaximum n : ℝ)) ∧
    |∑ j, (means j - μ)| ≤
      ((5 : ℝ) * (6109 / 231000) + ((16 + P : ℕ) : ℝ) * (257 / 500) +
        ((3 * (n / 450) : ℕ) : ℝ) / 235) * (poolMaximum n : ℝ) := by
  dsimp only
  let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
  let means := fun j : FWFourStageIndex n P =>
    (∑ i, (((entry a (cells ((j, i), false)) : ℝ) + entry a (cells ((j, i), true))) / 2)) /
      ((6 * (n + 8) : ℕ) : ℝ)
  let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
  have hb := fw_bridge_wide_stage_means_bound_of_theta bmor lower upper hnlo hnhi
    hrect hseed hwide hoff hs choice br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
    initial batches hvalid blocks hlen a hdiag hord hplaced hmatched
  dsimp only at hb
  have hc : ∀ j, |means j - μ| ≤ (257 / 500 : ℝ) * (poolMaximum n : ℝ) := by
    intro j
    exact fw_four_stage_mean_coarse_of_theta bmor lower upper hnlo hnhi (by omega) a cells j
  have hseed' : ∀ j : Fin 16, |means (Sum.inl (Sum.inl (Sum.inr j))) - μ| ≤
      (257 / 500 : ℝ) * (poolMaximum n : ℝ) := fun j => hc _
  have hgrowth' : ∀ j : Fin P, |means (Sum.inr j) - μ| ≤
      (257 / 500 : ℝ) * (poolMaximum n : ℝ) := fun j => hc _
  refine ⟨hseed', hgrowth', ?_⟩
  exact fw_four_family_sum_abs_bound (poolMaximum n : ℝ) (fun j => means j - μ)
    hb.1 hseed' hb.2 hgrowth'

end
end Sude
