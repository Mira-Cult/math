import Sude.FWSeedFullOffsetConcentration
import Sude.RetainedMidpointNoAvailability

/-! Same-square seed concentration under the selected source-width budget. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-! Same-witness seed concentration under selected-source width bounds only. -/
theorem fw_seed_source_concentration {n L : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (choice : Fin L → Bool) (hchoice : choice = fwBridgeSeedRectangleChoice hrect hseed otherChoice)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows sr)
    (packedCols : LayerPacking.PackedLayers reservedCols sc)
    (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hsd : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      entry old (packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (prefixRectangleInput (by omega) x)))
    (hso : ∀ x, entry old (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x)))
    (z V : ℝ)
    (hmax : ∀ i ∈ kept,
      sortedSeedReal candidates 17 (6 * (n + 8)) hcard (i * (6 * (n + 8)) + (6 * (n + 8) - 1)) -
      sortedSeedReal candidates 17 (6 * (n + 8)) hcard (i * (6 * (n + 8))) ≤ z)
    (hsource : 3 * 6 * (∑ i ∈ kept,
      (sortedSeedReal candidates 17 (6 * (n + 8)) hcard (i * (6 * (n + 8)) + (6 * (n + 8) - 1)) -
       sortedSeedReal candidates 17 (6 * (n + 8)) hcard (i * (6 * (n + 8)))) ^ 2) + 4 * z ^ 2 ≤ V) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let line := fun l : Fin ((n+n)+2) => fun c => c ∈ physicalAllLineCells l
    let weights := fun l j q => physicalPairLineWeight cells (line l) (j, q)
    let values := fun j q => (((entry grown (cells ((j, q), false)) : ℝ) +
      entry grown (cells ((j, q), true))) / 2)
    let B := Real.sqrt (V * Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) / 2)
    ∃ (ω : Fin 16 → Equiv.Perm (Fin (6 * (n + 8)))) (b : Cell n ≃ Fin (n*n)),
      (∀ j i side, entry b (cells ((j, i), side)) = entry grown (cells ((j, ω j i), side))) ∧
      (∀ c, c ∉ Set.range cells → entry b c = entry grown c) ∧
      (∀ j, Finset.univ.image (fun x : Fin (6 * (n + 8)) × Bool =>
        entry b (cells ((j, x.1), x.2))) =
        Finset.univ.image (fun x : Fin (6 * (n + 8)) × Bool =>
        entry grown (cells ((j, x.1), x.2)))) ∧
      Finset.univ.image (fun x => entry b (cells x)) =
        retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub ∧
      (∀ j i, entry b (cells ((j, i), true)) = entry b (cells ((j, i), false)) + 2) ∧
      (∀ l, |stageLineCentered (fun _ _ => Finset.univ) weights values l ω| ≤ B) ∧
      (∀ l, |(∑ c ∈ (Finset.univ.image cells).filter (line l), (entry b c : ℝ)) -
        (∑ j, ((∑ q, weights l j q) * ((∑ q, values j q) / ((6 * (n + 8) : ℕ) : ℝ)))) -
        (∑ p, physicalPairLineOrientation cells (line l) p * ((2 : ℝ) / 2))| ≤ B) := by
  classical
  have hQ : 0 < 6 * (n + 8) := by omega
  let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  let midpoint := retainedStageMidpoint candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept
  let lo : Fin 16 → ℝ := fun j => midpoint j ⟨0, hQ⟩
  let upper : Fin 16 → ℝ := fun j => midpoint j ⟨6 * (n + 8) - 1, by omega⟩
  have hmid := (fw_seed_existing_midpoints_and_injective candidates hcard kept hsub hkept hinj
    hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc old grown hfixed hsd hso).2
  have hvalues : ∀ j q, (((entry grown (cells ((j, q), false)) : ℝ) +
      entry grown (cells ((j, q), true))) / 2) ∈ Set.Icc (lo j) (upper j) := by
    intro j q
    rw [hmid j q]
    exact retainedStageMidpoint_bounds_no_availability candidates 17 16 (6 * (n + 8)) 2
      hcard kept hsub hkept hQ j q
  have hwidth : ∀ j, (upper j - lo j) ^ 2 ≤ z ^ 2 := by
    intro j
    exact retainedStage_midpoint_width_sq_le_no_availability candidates 17 16 (6 * (n + 8)) 2
      hcard kept hsub hkept hQ z hmax j
  have hbudget : 18 * (∑ j, (upper j - lo j) ^ 2) + 4 * z ^ 2 ≤ V := by
    have h := retainedStage_source_width_budget_no_availability candidates 17 16 (6 * (n + 8)) 2
      hcard kept hsub hkept hQ 6 z V hsource
    norm_num at h ⊢
    exact h
  exact fw_seed_full_offset_concentration candidates hcard kept hsub hkept hinj hrect hseed hwide hs hL
    otherChoice choice hchoice rows cols hr hc sr sc hsr hsc wr wc hwr hwc reservedRows reservedCols
    packedRows packedCols old grown hfixed hsd hso lo upper z V hvalues hwidth hbudget

end
end Sude
