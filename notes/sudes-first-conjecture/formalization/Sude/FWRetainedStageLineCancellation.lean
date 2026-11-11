import Sude.FWActualStageLineCancellation
import Sude.FWSeedExistingMidpoints
import Sude.FWWheelWitnessTraceStock
import Sude.FWCombinedPhysicalStageFamily
import Sude.FWFullReservationNonempty
import Sude.FWRoleCellOccupancy
import Sude.FWFullReservationLineIncidence

/-! Same-square retained seed and growth inputs feed exact signed cancellation.
No theta existence, concentration transfer, or full-line bound is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- Retained seed values and screened trace stock supply the actual seed and
growth stage data on the same reallocated square; no witness is constructed. -/
theorem fw_retained_stage_each_line_signed_cancellation {n P : ℕ} {final : Finset ℕ} {last : ℕ} {growthStages : List BTSelectedStage}
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
    (batches : ℕ → List DoublePair)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (old grown b : Cell n ≃ Fin (n * n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hsd : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      entry old (packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (prefixRectangleInput (by omega) x)))
    (hso : ∀ x, entry old (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x)))
    (hset : Finset.univ.image (fun x => entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x)) =
      retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 final last growthStages)
    (hlen : growthStages.length = P)
    (hplaced : ∀ x : PrefixPhysicalInputs P 6 3 n,
      entry grown (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc x) =
        (trace.poolValues hlen (by
          intro p hp
          exact mem_poolFinset.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).1)
          (prefixPhysicalInput (by omega) (by omega) x)).val)
    (hgrowthPres : ∀ x : PrefixPhysicalInputs P 6 3 n,
      entry b (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc x) =
      entry grown (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc x))
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
    let mean := Sum.elim (physicalStageMidpointAverage b seed) (physicalStageMidpointAverage b growth)
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let A : ℝ := ∑ j ∈ selected, (mean j - μ)
    let O : ℝ := (∑ z ∈ roles \ selected.biUnion cells, (entry b z : ℝ)) -
      ((roles \ selected.biUnion cells).card : ℝ) * μ
    let D : ℝ := (∑ z ∈ full \ roles, (entry b z : ℝ)) - ((full \ roles).card : ℝ) * μ
    let N : ℝ := (n * n - (12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) + 96 * (238 - P)) : ℕ)
    let S := 5 + 16 + 3 * (n / 450) + P
    let cancellation := fun q : ℕ =>
      let k : ℝ := (n - 12 * S - q : ℕ)
      2 * (6 : ℝ) * A + k * (centralEntriesMean (actualUnusedPool b full) centralPoolValue - μ) =
        (2 * (6 : ℝ) * A / N) * (((n : ℝ) + 8) * (q : ℝ) -
          96 * ((238 : ℝ) - P) - 8 * n) - k * (O + D) / N
    (∀ r : Fin n, ∃ q : ℕ, (q = 0 ∨ q = 2) ∧
      (LayerPacking.rowUsed full r).card = 12 * S + q ∧ 12 * S + q ≤ n ∧ cancellation q) ∧
    (∀ c : Fin n, ∃ q : ℕ, (q = 0 ∨ q = 2) ∧
      (LayerPacking.colUsed full c).card = 12 * S + q ∧ 12 * S + q ≤ n ∧ cancellation q) := by
  have hpool : ∀ p ∈ ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks, p ∈ pool n := by
    intro p hp
    exact mem_poolFinset.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).1
  have hstockSep : Disjoint (((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) := by
    exact Finset.sdiff_disjoint
  have hseedInj : Function.Injective (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) :=
    (fw_seed_existing_midpoints_and_injective candidates hcard kept hsub hkept hinj
      hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc old grown hfixed hsd hso).1
  have hseedValues : ∀ x, entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x) ∈
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks := by
    intro x
    have hx : entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x) ∈
        retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub := by
      rw [← hset]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hplacedB : ∀ x : PrefixPhysicalInputs P 6 3 n,
      entry b (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc x) =
        (trace.poolValues hlen hpool (prefixPhysicalInput (by omega) (by omega) x)).val := by
    intro x
    rw [hgrowthPres x]
    exact hplaced x
  exact fw_actual_stage_each_line_signed_cancellation hn hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
    b trace hlen hpool (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
    hstockSep hseedInj hseedValues hplacedB selected

end
end Sude
