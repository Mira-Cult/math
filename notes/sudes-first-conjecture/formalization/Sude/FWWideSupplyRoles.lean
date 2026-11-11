import Sude.FWWideSelectedPlacement
import Sude.FWWideSpatialReservation

/-! Connect FW's selected matched-bin supply to supplied wide-role geometry.
No later growth layout or numerical mean estimate is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- FW's reflected bin geometry orders every actual low-bin entry below
every actual high-bin entry. -/
theorem fw_reflected_bins_cross_order {n : ℕ} (m : ℝ)
    (hX : (100 : ℝ) ≤ poolMaximum n)
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ) * (poolMaximum n : ℝ)) :
    ∀ a ∈ Finset.univ.biUnion
      (bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))),
      ∀ b ∈ Finset.univ.biUnion
        (bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))), a < b := by
  intro a ha b hb
  obtain ⟨i, _, hai⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨j, _, hbj⟩ := Finset.mem_biUnion.mp hb
  obtain ⟨hends, _, hcross, _⟩ := fw_reflected_bin_geometry m (poolMaximum n) hX hmlo hmhi
  have hlow := (mem_apInterval_iff _ _ 2 1 (by linarith [(hends (i, false)).1])
    (by linarith [(hends (i, false)).1, (hends (i, false)).2.1]) a).mp hai
  have hhigh := (mem_apInterval_iff _ _ 2 1 (by linarith [(hends (j, true)).1])
    (by linarith [(hends (j, true)).1, (hends (j, true)).2.1]) b).mp hbj
  have hreal : (a : ℝ) < b := lt_of_le_of_lt (hlow.2.2.1.trans (hcross i j)) hhigh.2.1
  exact_mod_cast hreal

/-- Select the FW10 wide blocks avoiding the actual bridge and retained-seed
values and install those same blocks in the supplied source roles. Prior
cells stay fixed and all target cells avoid the spatial exclusion; unrelated
old entries in the spatial exclusion are not asserted fixed. -/
theorem fw_select_and_install_wide_roles {n L : ℕ}
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (m : ℝ)
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ) * (poolMaximum n : ℝ))
    (batches : ℕ → List DoublePair)
    (hlenBridge : ∀ j < 5, (batches j).length = 3 * (n + 8))
    (retained : Finset ℕ) (hretained : retained.card = 2 * (6 * (n + 8)) * 16)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (a : Cell n ≃ Fin (n * n)) (base prior spatial : Finset (Cell n))
    (hrectbase : packedRectangleSupport hs choice ⊆ base) (hprior : prior ⊆ base)
    (hpriorValues : ∀ c ∈ prior,
      entry a c ∈ priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained)
    (hdiagfree : ∀ x : Fin ((3 * (n / 450)) * (4 * 6)) × Fin 4,
      packedRectangleCorner hs choice (fwWideRectangle hwide x.1, x.2) ∉ prior)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (hrows : LayerPacking.PackedLayers base rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (base ∪ LayerPacking.layersSupport rows)) cols)
    (hdisjoint : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)))
    (hspatial : ∀ x, fwWidePhysicalCells hwide hs choice rows cols hr hc x ∉ spatial) :
    let low := bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    let high := bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    ∃ (blocks : List DoublePair)
      (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
      (b : Cell n ≃ Fin (n * n)),
      (∀ block ∈ blocks, block.MatchedValid low high) ∧
      blocks.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ block ∈ blocks, Disjoint block.footprint
        (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained)) ∧
      (∀ c ∈ prior, entry b c = entry a c) ∧
      (∀ x : FWWideInputs n,
        entry b (fwWidePhysicalCells hwide hs choice rows cols hr hc x) =
          doublePairSequenceEndpoint blocks
            (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2)) ∧
      (∀ x, fwWidePhysicalCells hwide hs choice rows cols hr hc x ∉ spatial) ∧
      (let cells : Fin blocks.length × Fin 4 → Cell n := fun x =>
        fwWidePhysicalCells hwide hs choice rows cols hr hc
          ((Equiv.ofBijective (fwWideFlatSlot n) (fwWideFlatSlot_bijective n)).symm
            (Fin.cast hlen x.1, x.2))
       fwInstalledPairBounds m (poolMaximum n) blocks b cells ∧
       ∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        entry b (cells (i, 1)) = entry b (cells (i, 0)) + gap ∧
        entry b (cells (i, 2)) = entry b (cells (i, 3)) + gap ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n) := by
  dsimp only
  let roleEquiv := Equiv.ofBijective (fwWideFlatSlot n) (fwWideFlatSlot_bijective n)
  let cells := fun x => fwWidePhysicalCells hwide hs choice rows cols hr hc (roleEquiv.symm x)
  obtain ⟨hphysicalInj, hphysicalFree⟩ :=
    fwWidePhysicalCells_geometry hwide hs choice base prior hrectbase hprior hdiagfree
      rows cols hr hc hrows hcols hdisjoint
  have hcells : Function.Injective cells := hphysicalInj.comp roleEquiv.symm.injective
  obtain ⟨blocks, hlen, temp, hmatched, hpair, hav, hplaced, _, _, _, _⟩ :=
    fw_wide_install_avoiding_spatial_reservation bmor upper lower sharp hnlo hnhi m hmlo hmhi
      batches hlenBridge retained hretained a cells spatial prior hcells
      (fun x => hspatial _) (fun x => hphysicalFree _) hpriorValues
  have hpool : ∀ block ∈ blocks, ∀ side, block.endpoint side ∈ pool n := by
    intro block hb side
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hb
    have hp : entry temp (cells (Fin.cast hlen i, side)) ∈ pool n := by
      rw [← entry_range temp]
      exact ⟨_, rfl⟩
    rw [hplaced (i, side)] at hp
    exact hp
  have hXnat : 100 ≤ poolMaximum n :=
    (by decide : 100 ≤ 4 * 2 ^ 30).trans (le_of_lt (fw_poolMaximum_gt_four_seed lower hnlo))
  have hX : (100 : ℝ) ≤ poolMaximum n := by exact_mod_cast hXnat
  have horder := fw_reflected_bins_cross_order m hX hmlo hmhi
  obtain ⟨b, _, hfixed, hbounds, hgap, hroles⟩ :=
    fw_install_selected_wide_roles m hX hmlo hmhi blocks hlen hmatched hpair horder hpool
      (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained) hav hwide hs choice
      a base prior hrectbase hprior hpriorValues hdiagfree rows cols hr hc hrows hcols hdisjoint
  exact ⟨blocks, hlen, b, hmatched, hpair, hav, hfixed, hroles, hspatial, hbounds, hgap⟩

end
end Sude
