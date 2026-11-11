import Sude.FWSeedOrdinarySlots

/-! Install the retained ordinary seed pairs after their rectangles,
preserving supplied bridge cells and all installed seed rectangle corners. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- The earlier selected retained seed rectangle corners, in the shared RP1
packing. -/
def fwSeedRectangleCells {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) : Finset (Cell n) :=
  (Finset.univ : Finset (Fin (16 * (4 * 6)) × Fin 4)).image
    (fun x => packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2))

/-- Install the ordinary retained seed endpoints in supplied packed layers.
The supplied `prior` cells contain bridge values; seed rectangle corners are
already placed with the same retained witnesses. Geometry reserves the entire
RP1 support and `prior` from new cells. The extension fixes the `prior`
entries and the selected seed-rectangle corners. -/
theorem fw_install_retained_seed_ordinary
    (n L : ℕ) (candidates : Finset ℕ)
    (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (bridges : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard x ∈
      poolFinset n \ bridges)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (a : Cell n ≃ Fin (n * n)) (prior layoutBase : Finset (Cell n))
    (hprior : prior ⊆ layoutBase)
    (hrectbase : packedRectangleSupport hs choice ⊆ layoutBase)
    (hpriorValues : ∀ c ∈ prior, entry a c ∈ bridges)
    (hdiag : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      entry a (packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept
            (prefixRectangleInput (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) x)))
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 16 * 3)
    (hc : cols.length = 16 * 3)
    (hrows : LayerPacking.PackedLayers layoutBase rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (layoutBase ∪ LayerPacking.layersSupport rows)) cols)
    (hdisjoint : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols))) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ x, entry b (fwSeedOrdinaryCells rows cols hr hc x) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x))) ∧
      (∀ c ∈ prior, entry b c = entry a c) ∧
      (∀ x : Fin (16 * (4 * 6)) × Fin 4,
        entry b (packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) =
          entry a (packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2))) ∧
      (∀ (i : Fin (16 * 3)) (e : Fin n),
        entry b (fwSeedOrdinaryCells rows cols hr hc (Sum.inl (i, (e, true)))) =
          entry b (fwSeedOrdinaryCells rows cols hr hc (Sum.inl (i, (e, false)))) + 2 ∧
        entry b (fwSeedOrdinaryCells rows cols hr hc (Sum.inr (i, (e, true)))) =
          entry b (fwSeedOrdinaryCells rows cols hr hc (Sum.inr (i, (e, false)))) + 2) := by
  let seedCells := fwSeedRectangleCells hseed hs choice
  let reserved := prior ∪ seedCells
  let values := retainedSeedPoolValues candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept bridges hav
  let v : FWSeedOrdinaryInputs n → pool n := fun x => values (fwSeedOrdinaryInput n x)
  have hvi : Function.Injective values :=
    retainedSeedPoolValues_injective candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept bridges hav hinj
  have hv : Function.Injective v := hvi.comp (fwSeedOrdinaryInput_injective n)
  obtain ⟨hcells, hfree, _⟩ := fwSeedOrdinaryCells_geometry hs choice layoutBase hrectbase
    rows cols hr hc hrows hcols hdisjoint
  have hseedSub : seedCells ⊆ layoutBase := by
    intro c hc'
    obtain ⟨⟨t, side⟩, _, rfl⟩ := Finset.mem_image.mp hc'
    apply hrectbase
    exact Finset.mem_image.mpr ⟨(fwSeedRectangle hseed t, side), Finset.mem_univ _, rfl⟩
  have hnew : ∀ x, fwSeedOrdinaryCells rows cols hr hc x ∉ reserved := by
    intro x hx
    apply hfree x
    rcases Finset.mem_union.mp hx with hp | hs'
    · exact hprior hp
    · exact hseedSub hs'
  have havoid : ∀ x c, c ∈ reserved → (v x).val ≠ entry a c := by
    intro x c hc' heq
    rcases Finset.mem_union.mp hc' with hc' | hc'
    · have hnot := retainedSeedPoolValues_avoid candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept bridges hav
        (fwSeedOrdinaryInput n x)
      apply hnot
      change (v x).val ∈ bridges
      rw [heq]
      exact hpriorValues c hc'
    · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hc'
      apply fwSeedOrdinaryInput_ne_rectangle n x y
      apply hvi
      apply Subtype.ext
      exact heq.trans (hdiag y)
  obtain ⟨b, hplaced, hfixed⟩ := place_distinct_pool_entries_preserving a
    (fwSeedOrdinaryCells rows cols hr hc) v reserved hcells hv hnew havoid
  refine ⟨b, hplaced, ?_, ?_, ?_⟩
  · intro c hc'
    exact hfixed c (Finset.mem_union_left _ hc')
  · intro x
    exact hfixed _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))
  · intro i e
    constructor
    · rw [hplaced (Sum.inl (i, (e, true))), hplaced (Sum.inl (i, (e, false)))]
      have hg := retainedSeedPoolValues_gap candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept bridges hav
        (finProdFinEquiv.symm i).1
        (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
          (0, (finProdFinEquiv.symm i).2, e))
      simpa [v, values, fwSeedOrdinaryInput, prefixNetworkInput, prefixOrdinaryInput] using hg
    · rw [hplaced (Sum.inr (i, (e, true))), hplaced (Sum.inr (i, (e, false)))]
      have hg := retainedSeedPoolValues_gap candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept bridges hav
        (finProdFinEquiv.symm i).1
        (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
          (1, (finProdFinEquiv.symm i).2, e))
      simpa [v, values, fwSeedOrdinaryInput, prefixNetworkInput, prefixOrdinaryInput] using hg

end
end Sude
