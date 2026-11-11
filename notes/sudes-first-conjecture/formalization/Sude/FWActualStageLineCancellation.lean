import Sude.FWGeometryLineCancellationNonempty
import Sude.FWCombinedPhysicalStageFamily
import Sude.FWFullReservationNonempty
import Sude.FWRoleCellOccupancy
import Sude.FWFullReservationLineIncidence

/-! Exact signed cancellation for supplied actual FW seed and growth stages.
No theta existence, numerical mean, or full-line bound is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384

/-- The actual same-square seed and growth pair families supply the selected
stages; every line has its own q in {0,2} and the same-q signed identity. -/
theorem fw_actual_stage_each_line_signed_cancellation {g n P : ℕ} {initial final : Finset ℕ} {radius last : ℕ} {growthStages : List BTSelectedStage}
    (hn : 19485 ≤ n) (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice)
      (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (a : Cell n ≃ Fin (n * n))
    (trace : BTGrowingTrace g (6 * (n + 8)) initial radius final last growthStages)
    (hlen : growthStages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (earlyValues : Finset ℕ) (hstockSep : Disjoint initial earlyValues)
    (hseedInj : Function.Injective (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc))
    (hseedValues : ∀ x, entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x) ∈ earlyValues)
    (hplaced : ∀ x : PrefixPhysicalInputs P 6 3 n,
      entry a (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc x) =
        (trace.poolValues hlen hpool (prefixPhysicalInput (by omega) (by omega) x)).val)
    (selected : Finset (Fin 16 ⊕ Fin P))
    :
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc
    let cells := combinedPhysicalPairStageCells seed growth
    let mean := Sum.elim (physicalStageMidpointAverage a seed) (physicalStageMidpointAverage a growth)
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let A : ℝ := ∑ j ∈ selected, (mean j - μ)
    let O : ℝ := (∑ z ∈ roles \ selected.biUnion cells, (entry a z : ℝ)) -
      ((roles \ selected.biUnion cells).card : ℝ) * μ
    let D : ℝ := (∑ z ∈ full \ roles, (entry a z : ℝ)) - ((full \ roles).card : ℝ) * μ
    let N : ℝ := (n * n - (12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) + 96 * (238 - P)) : ℕ)
    let S := 5 + 16 + 3 * (n / 450) + P
    let cancellation := fun q : ℕ =>
      let k : ℝ := (n - 12 * S - q : ℕ)
      2 * (6 : ℝ) * A + k * (centralEntriesMean (actualUnusedPool a full) centralPoolValue - μ) =
        (2 * (6 : ℝ) * A / N) * (((n : ℝ) + 8) * (q : ℝ) -
          96 * ((238 : ℝ) - P) - 8 * n) - k * (O + D) / N
    (∀ r : Fin n, ∃ q : ℕ, (q = 0 ∨ q = 2) ∧
      (LayerPacking.rowUsed full r).card = 12 * S + q ∧ 12 * S + q ≤ n ∧ cancellation q) ∧
    (∀ c : Fin n, ∃ q : ℕ, (q = 0 ∨ q = 2) ∧
      (LayerPacking.colUsed full c).card = 12 * S + q ∧ 12 * S + q ≤ n ∧ cancellation q) := by
  dsimp only
  let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
    (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc
  let cells := combinedPhysicalPairStageCells seed growth
  let mean := Sum.elim (physicalStageMidpointAverage a seed) (physicalStageMidpointAverage a growth)
  have hfam := fw_combined_physical_stage_family trace hlen hpool earlyValues hstockSep
    hrect hseed hwide (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
    hoff hs choice br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
    a hseedInj hseedValues hplaced
  dsimp only at hfam
  have hdis : Set.PairwiseDisjoint (↑selected : Set (Fin 16 ⊕ Fin P)) cells := by
    intro i hi j hj hij
    exact hfam.1 (Set.mem_univ i) (Set.mem_univ j) hij
  have hcard : ∀ j ∈ selected, (cells j).card = 2 * 6 * (n + 8) := by
    intro j hj
    have hh := hfam.2.1 j
    change (cells j).card = 12 * (n + 8) at hh
    omega
  have hsum : ∀ j ∈ selected,
      (∑ z ∈ cells j, (entry a z : ℝ)) = (2 * 6 * (n + 8) : ℕ) * mean j := by
    intro j hj
    have hh := hfam.2.2.1 j
    change (∑ z ∈ cells j, (entry a z : ℝ)) = ((12 * (n + 8) : ℕ) : ℝ) * mean j at hh
    simpa only [show 2 * 6 * (n + 8) = 12 * (n + 8) by omega] using hh
  have hstage := hfam.2.2.2 selected
  exact fw_geometry_each_line_signed_cancellation_of_nonempty hn hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
    a selected cells 6 mean hdis hcard hsum hstage

end
end Sude
