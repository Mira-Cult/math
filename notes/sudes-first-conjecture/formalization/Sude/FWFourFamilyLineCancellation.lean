import Sude.FWFourFamilyStageTotals
import Sude.FWGeometryLineCancellationNonempty

/-! Exact four-family signed cancellation: all actual active roles belong to
one physical stage, so only the actual spare reservation remains. No bound,
theta witness, or diagonal assertion is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- Every row and column has its actual full-reservation incidence and exact
four-family cancellation, with no active-role remainder. -/
theorem fw_four_family_each_line_signed_cancellation {n P : ℕ}
    (hn : 19485 ≤ n)
    (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
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
    (a : Cell n ≃ Fin (n * n)) :
    let f := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
    let cells := f ∘ fwFourStageInputEquiv n P
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    let means := fun j : FWFourStageIndex n P =>
      (∑ i, (((entry a (cells ((j, i), false)) : ℝ) + entry a (cells ((j, i), true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let A : ℝ := ∑ j, (means j - μ)
    let D : ℝ := (∑ z ∈ full \ roles, (entry a z : ℝ)) - ((full \ roles).card : ℝ) * μ
    let N : ℝ := (n * n - (12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) + 96 * (238 - P)) : ℕ)
    let S := 5 + 16 + 3 * (n / 450) + P
    let cancellation := fun q : ℕ =>
      let k : ℝ := (n - 12 * S - q : ℕ)
      2 * (6 : ℝ) * A + k * (centralEntriesMean (actualUnusedPool a full) centralPoolValue - μ) =
        (2 * (6 : ℝ) * A / N) * (((n : ℝ) + 8) * (q : ℝ) -
          96 * ((238 : ℝ) - P) - 8 * n) - k * D / N
    (∀ r : Fin n, ∃ q : ℕ, (q = 0 ∨ q = 2) ∧
      (LayerPacking.rowUsed full r).card = 12 * S + q ∧ 12 * S + q ≤ n ∧ cancellation q) ∧
    (∀ c : Fin n, ∃ q : ℕ, (q = 0 ∨ q = 2) ∧
      (LayerPacking.colUsed full c).card = 12 * S + q ∧ 12 * S + q ≤ n ∧ cancellation q) := by
  classical
  dsimp only
  let f := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
  let cells := f ∘ fwFourStageInputEquiv n P
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
  let stages := fun j : FWFourStageIndex n P =>
    Finset.univ.image (fun x : Fin (6 * (n + 8)) × Bool => cells ((j, x.1), x.2))
  let means := fun j : FWFourStageIndex n P =>
    (∑ i, (((entry a (cells ((j, i), false)) : ℝ) + entry a (cells ((j, i), true))) / 2)) /
      ((6 * (n + 8) : ℕ) : ℝ)
  have ht := fw_four_family_stage_totals hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols a
  dsimp only at ht
  have hcover : Finset.univ.biUnion stages = roles := ht.2.2.2.2.2
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset (FWFourStageIndex n P)) : Set _) stages := by
    simpa only [Finset.coe_univ] using ht.2.2.1
  have hcard : ∀ j ∈ (Finset.univ : Finset (FWFourStageIndex n P)), (stages j).card = 2 * 6 * (n + 8) := by
    intro j _
    change (stages j).card = 12 * (n + 8)
    exact ht.2.2.2.1 j
  have hsum : ∀ j ∈ (Finset.univ : Finset (FWFourStageIndex n P)),
      (∑ z ∈ stages j, (entry a z : ℝ)) = ((2 * 6 * (n + 8) : ℕ) : ℝ) * means j := by
    intro j _
    change (∑ z ∈ stages j, (entry a z : ℝ)) = ((12 * (n + 8) : ℕ) : ℝ) * means j
    exact ht.2.2.2.2.1 j
  have h := fw_geometry_each_line_signed_cancellation_of_nonempty hn hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
    a Finset.univ stages 6 means hdis hcard hsum (hcover.subset)
  dsimp only at h
  have hO : roles \ Finset.univ.biUnion stages = ∅ := by rw [hcover, Finset.sdiff_self]
  rw [hO] at h
  norm_num only at h
  simpa only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_mul, sub_zero,
    zero_add, show (2 : ℝ) * 6 = 12 by norm_num] using h

end
end Sude
