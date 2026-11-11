import Sude.FWRetainedStageLineCancellation
import Sude.FullReservationCancellationEnvelope
import Sude.FWSeedExistingMidpoints
import Sude.FWWheelWitnessTraceStock
import Sude.FWCombinedPhysicalStageFamily
import Sude.FWFullReservationNonempty
import Sude.FWRoleCellOccupancy
import Sude.FWFullReservationLineIncidence

/-! A supplied same-square budget bounds each retained-stage cancellation.
No theta existence, numerical budget, or full-line bound is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- The same retained stages and physical reservation give each line an exact
cancellation and an envelope using explicit supplied deviation budgets. -/
theorem fw_retained_stage_each_line_cancellation_envelope {n P : ℕ} {final : Finset ℕ} {last : ℕ} {growthStages : List BTSelectedStage}
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
    (Amax Omax Dmax : ℝ) (hAmax : 0 ≤ Amax) (hOmax : 0 ≤ Omax) (hDmax : 0 ≤ Dmax)
    (hbudgets :
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
    |A| ≤ Amax ∧ |O| ≤ Omax ∧ |D| ≤ Dmax)
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
    let envelope := fun q : ℕ =>
      |12 * A + ((n - 12 * S - q : ℕ) : ℝ) *
        (centralEntriesMean (actualUnusedPool b full) centralPoolValue - μ)| ≤
        (12 * Amax * (8 * (n : ℝ) + 96 * ((238 : ℝ) - P)) +
          ((n : ℝ) - ((12 * S : ℕ) : ℝ)) * (Omax + Dmax)) / N
    (∀ r : Fin n, ∃ q : ℕ, (q = 0 ∨ q = 2) ∧
      (LayerPacking.rowUsed full r).card = 12 * S + q ∧ 12 * S + q ≤ n ∧ cancellation q ∧ envelope q) ∧
    (∀ c : Fin n, ∃ q : ℕ, (q = 0 ∨ q = 2) ∧
      (LayerPacking.colUsed full c).card = 12 * S + q ∧ 12 * S + q ≤ n ∧ cancellation q ∧ envelope q) := by
  dsimp only at hbudgets ⊢
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
  let S := 5 + 16 + 3 * (n / 450) + P
  let N : ℝ := (n * n - (12 * S * (n + 8) + 96 * (238 - P)) : ℕ)
  have hNnat : 0 < n * n - (12 * S * (n + 8) + 96 * (238 - P)) := by
    have hh := fw_full_reservation_card_formula_lt hn hP
    dsimp [S] at hh ⊢
    omega
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hNnat
  have hnReal : (19485 : ℝ) ≤ n := by exact_mod_cast hn
  have hPReal : (P : ℝ) ≤ 238 := by exact_mod_cast hP
  have hb : 0 ≤ 96 * ((238 : ℝ) - P) := by linarith
  have hcancel := fw_retained_stage_each_line_signed_cancellation hn hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
    batches candidates hcard kept hsub hkept hinj blocks old grown b hfixed hsd hso hset trace hlen
    hplaced hgrowthPres selected
  dsimp only at hcancel
  have hbound (q : ℕ) (hq : q = 0 ∨ q = 2) (hline : 12 * S + q ≤ n)
      (hid : 12 * A + ((n - 12 * S - q : ℕ) : ℝ) *
          (centralEntriesMean (actualUnusedPool b full) centralPoolValue - μ) =
        (12 * A / N) * (((n : ℝ) + 8) * (q : ℝ) - 96 * ((238 : ℝ) - P) - 8 * n) -
          ((n - 12 * S - q : ℕ) : ℝ) * (O + D) / N) :
      |12 * A + ((n - 12 * S - q : ℕ) : ℝ) *
        (centralEntriesMean (actualUnusedPool b full) centralPoolValue - μ)| ≤
        (12 * Amax * (8 * (n : ℝ) + 96 * ((238 : ℝ) - P)) +
          ((n : ℝ) - ((12 * S : ℕ) : ℝ)) * (Omax + Dmax)) / N := by
    have hrq : 0 ≤ ((12 * S : ℕ) : ℝ) + (q : ℝ) ∧
        ((12 * S : ℕ) : ℝ) + (q : ℝ) ≤ (n : ℝ) := by
      constructor
      · positivity
      · exact_mod_cast hline
    have hqReal : (q : ℝ) = 0 ∨ (q : ℝ) = 2 := by
      rcases hq with hq | hq <;> simp [hq]
    have hk : ((n - 12 * S - q : ℕ) : ℝ) =
        (n : ℝ) - ((12 * S : ℕ) : ℝ) - (q : ℝ) := by
      rw [Nat.cast_sub (by omega : q ≤ n - 12 * S), Nat.cast_sub (by omega : 12 * S ≤ n)]
    rw [hk] at hid ⊢
    exact full_reservation_cancellation_envelope (n : ℝ) ((12 * S : ℕ) : ℝ) (q : ℝ)
      (96 * ((238 : ℝ) - P)) N A O D
      (centralEntriesMean (actualUnusedPool b full) centralPoolValue) μ Amax Omax Dmax
      hnReal hb hN hrq hqReal hAmax hOmax hDmax hbudgets.1 hbudgets.2.1 hbudgets.2.2 hid
  constructor
  · intro row
    obtain ⟨q, hq, hcount, hline, hid⟩ := hcancel.1 row
    have hid' := hid
    norm_num only at hid'
    exact ⟨q, hq, hcount, hline, hid, hbound q hq hline hid'⟩
  · intro col
    obtain ⟨q, hq, hcount, hline, hid⟩ := hcancel.2 col
    have hid' := hid
    norm_num only at hid'
    exact ⟨q, hq, hcount, hline, hid, hbound q hq hline hid'⟩

end
end Sude
