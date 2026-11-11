import Sude.FWWidePhysicalSlots
import Sude.FWPhysicalSupplyWithGeometry
import Sude.FWInstalledGap

/-! Install a supplied selected FW wide-block list in supplied source role
cells. Supply, earlier layout construction, and later growth remain separate. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- Given actual pairwise-disjoint matched wide blocks and valid physical
role geometry, install those exact blocks while preserving all prior cells.
The ordering, pool membership, avoidance and geometry conditions are
explicit; the theorem does not select blocks or construct the layout. -/
theorem fw_install_selected_wide_roles {n L : ℕ}
    (m : ℝ) (hX : (100 : ℝ) ≤ poolMaximum n)
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ) * (poolMaximum n : ℝ))
    (blocks : List DoublePair)
    (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))))
    (hpair : blocks.Pairwise (fun x y => Disjoint x.footprint y.footprint))
    (horder : ∀ a ∈ Finset.univ.biUnion
        (bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))),
      ∀ b ∈ Finset.univ.biUnion
        (bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))), a < b)
    (hpool : ∀ block ∈ blocks, ∀ side, block.endpoint side ∈ pool n)
    (removed : Finset ℕ) (havoid : ∀ block ∈ blocks, Disjoint block.footprint removed)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (a : Cell n ≃ Fin (n * n)) (base prior : Finset (Cell n))
    (hrectbase : packedRectangleSupport hs choice ⊆ base) (hprior : prior ⊆ base)
    (hpriorValues : ∀ c ∈ prior, entry a c ∈ removed)
    (hdiagfree : ∀ x : Fin ((3 * (n / 450)) * (4 * 6)) × Fin 4,
      packedRectangleCorner hs choice (fwWideRectangle hwide x.1, x.2) ∉ prior)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (hrows : LayerPacking.PackedLayers base rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (base ∪ LayerPacking.layersSupport rows)) cols)
    (hdisjoint : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols))) :
    let cells : Fin blocks.length × Fin 4 → Cell n := fun x =>
      fwWidePhysicalCells hwide hs choice rows cols hr hc
        ((Equiv.ofBijective (fwWideFlatSlot n) (fwWideFlatSlot_bijective n)).symm
          (Fin.cast hlen x.1, x.2))
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ x, entry b (cells x) = doublePairSequenceEndpoint blocks x) ∧
      (∀ c ∈ prior, entry b c = entry a c) ∧
      fwInstalledPairBounds m (poolMaximum n) blocks b cells ∧
      (∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        entry b (cells (i, 1)) = entry b (cells (i, 0)) + gap ∧
        entry b (cells (i, 2)) = entry b (cells (i, 3)) + gap ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n) ∧
      (∀ x : FWWideInputs n,
        entry b (fwWidePhysicalCells hwide hs choice rows cols hr hc x) =
          doublePairSequenceEndpoint blocks
            (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2)) := by
  dsimp only
  let roleEquiv := Equiv.ofBijective (fwWideFlatSlot n) (fwWideFlatSlot_bijective n)
  let cells : Fin blocks.length × Fin 4 → Cell n := fun x =>
    fwWidePhysicalCells hwide hs choice rows cols hr hc
      (roleEquiv.symm (Fin.cast hlen x.1, x.2))
  obtain ⟨hphysicalInj, hphysicalFree⟩ :=
    fwWidePhysicalCells_geometry hwide hs choice base prior hrectbase hprior hdiagfree
      rows cols hr hc hrows hcols hdisjoint
  have hcells : Function.Injective cells := by
    rintro ⟨i, s⟩ ⟨j, t⟩ heq
    have hrole := roleEquiv.symm.injective (hphysicalInj heq)
    have hi : i = j := Fin.cast_injective hlen (congrArg Prod.fst hrole)
    have ht : s = t := congrArg Prod.snd hrole
    exact Prod.ext hi ht
  have hnew : ∀ x, cells x ∉ prior := fun x => hphysicalFree _
  let values : Fin blocks.length × Fin 4 → pool n := fun x =>
    ⟨doublePairSequenceEndpoint blocks x, hpool (blocks.get x.1) (List.get_mem blocks x.1) x.2⟩
  have hvalid : ∀ block ∈ blocks, block.valid
      (Finset.univ.biUnion (bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))))
      (Finset.univ.biUnion (bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n)))) :=
    fun block hb => (hmatched block hb).1
  have hvalues : Function.Injective values := by
    intro x y heq
    apply doublePairSequenceEndpoint_injective blocks _ _ horder hvalid hpair
    exact congrArg Subtype.val heq
  have hav : ∀ x c, c ∈ prior → (values x).val ≠ entry a c := by
    rintro ⟨i, side⟩ c hc' heq
    have hm : (blocks.get i).endpoint side ∈ removed := by
      change (blocks.get i).endpoint side = entry a c at heq
      rw [heq]
      exact hpriorValues c hc'
    exact Finset.disjoint_left.mp (havoid (blocks.get i) (List.get_mem blocks i))
      (DoublePair.endpoint_mem (blocks.get i) side) hm
  obtain ⟨b, hplaced, hfixed⟩ := place_distinct_pool_entries_preserving a cells values prior hcells hvalues hnew hav
  have hbounds : fwInstalledPairBounds m (poolMaximum n) blocks b cells := by
    intro i
    exact fw_installed_matched_block_bounds m (poolMaximum n) hX hmlo hmhi blocks b cells hmatched hplaced i
  have hgap : ∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
      entry b (cells (i, 1)) = entry b (cells (i, 0)) + gap ∧
      entry b (cells (i, 2)) = entry b (cells (i, 3)) + gap ∧
      (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n := by
    intro i
    exact fw_installed_matched_block_even_gap m (poolMaximum n) hX hmlo hmhi blocks b cells hmatched hplaced i
  refine ⟨b, hplaced, hfixed, hbounds, hgap, ?_⟩
  intro x
  have hx := hplaced (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2)
  have heq : cells (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2) =
      fwWidePhysicalCells hwide hs choice rows cols hr hc x := by
    change fwWidePhysicalCells hwide hs choice rows cols hr hc
      (roleEquiv.symm (Fin.cast hlen (Fin.cast hlen.symm (fwWideFlatSlot n x).1),
        (fwWideFlatSlot n x).2)) = _
    have hindex : (Fin.cast hlen (Fin.cast hlen.symm (fwWideFlatSlot n x).1),
        (fwWideFlatSlot n x).2) = roleEquiv x := by
      dsimp [roleEquiv]
    rw [hindex, roleEquiv.symm_apply_apply]
  rw [heq] at hx
  exact hx

end
end Sude
