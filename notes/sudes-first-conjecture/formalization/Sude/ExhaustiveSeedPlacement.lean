import Sude.PrefixAllocationCoverage
import Sude.NarrowSeedPlacement

/-! Connect exact retained-set coverage to the allocator's physical witness. -/
namespace Sude
noncomputable section

theorem prefixNetworkInput_cast_comp {P d r n Q k m : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q)
    (h₁ : k = m) (h₂ : m = P * r) (network : Fin 2)
    (x : Fin k × (Fin n × Bool)) :
    prefixNetworkInput hfit h₂ network (Fin.cast h₁ x.1, x.2) =
      prefixNetworkInput hfit (h₁.trans h₂) network x := by
  cases h₁
  rfl

/-- The allocator produces a single witness that preserves the old cells,
packs both networks, realizes their gaps, and uses every retained endpoint
in exactly one of the actual rectangle or network cells. -/
theorem install_retained_seed_pairs_exhaustively {n r P Q gap d layers L B : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q)
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P)
    (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = P * layers) (hclen : colPerms.length = P * layers)
    (hrderange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcderange : ∀ π ∈ colPerms, ∀ i, π i ≠ i)
    (base : Finset (Cell n)) (hrload : ∀ i, (LayerPacking.rowUsed base i).card ≤ B)
    (hcload : ∀ i, (LayerPacking.colUsed base i).card ≤ B)
    (hcapacity : 4 * ((B + 2) + 2 * rowPerms.length + 2 * colPerms.length) + 8 < n)
    (a : Cell n ≃ Fin (n * n)) (hbase : ∀ c ∈ base, entry a c ∈ initial)
    (hfree : ∀ x : Fin (P * (4 * d)) × Fin 4,
      packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2) ∉ base) :
    ∃ (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = rowPerms.length)
      (hcols : cols.length = colPerms.length) (b : Cell n ≃ Fin (n * n)),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers (base ∪ allocatedBridgeRectangleSupport hrect hs choice) rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        ((base ∪ allocatedBridgeRectangleSupport hrect hs choice) ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows) (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ x : Fin (P * (4 * d)) × Fin 4,
        entry b (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
          sortedSeedEndpoint candidates r Q gap hcard
            (retainedSeedSlot r P Q kept hsub hkept (prefixRectangleInput hdiag x))) ∧
      (∀ x, entry b (LayerPacking.sequenceCell rows x) =
        sortedSeedEndpoint candidates r Q gap hcard
          (retainedSeedSlot r P Q kept hsub hkept (prefixNetworkInput hfit (hrows.trans hrlen) 0 x))) ∧
      (∀ x, entry b (LayerPacking.sequenceCell cols x).swap =
        sortedSeedEndpoint candidates r Q gap hcard
          (retainedSeedSlot r P Q kept hsub hkept (prefixNetworkInput hfit (hcols.trans hclen) 1 x))) ∧
      (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
        entry b (e, (rows.get i).2 e) + variablePrefixNetworkGap (fun _ => gap) hrlen (Fin.cast hrows i) e) ∧
      (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
        entry b ((cols.get i).2 e, e) + variablePrefixNetworkGap (fun _ => gap) hclen (Fin.cast hcols i) e) ∧
      Function.Injective (prefixPhysicalCells hrect hs choice rows cols (hrows.trans hrlen) (hcols.trans hclen)) ∧
      Finset.univ.image (fun x => entry b
        (prefixPhysicalCells hrect hs choice rows cols (hrows.trans hrlen) (hcols.trans hclen) x)) =
          retainedSeedEndpoints candidates r Q gap hcard kept hsub ∧
      ∀ c ∈ base, entry b c = entry a c := by
  obtain ⟨rows, cols, hrows, hcols, b, hrmap, hcmap, hrpack, hcpack, hdis,
    hplaced, hrplaced, hcplaced, hrgap, hcgap, hfixed⟩ :=
    install_retained_seed_pairs candidates hcard kept hsub hkept initial hav hinj
      hfit hdiag hrect hs choice rowPerms colPerms hrlen hclen hrderange hcderange
      base hrload hcload hcapacity a hbase hfree
  have hrectangle : ∀ x : Fin (P * (4 * d)) × Fin 4,
      entry b (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
        sortedSeedEndpoint candidates r Q gap hcard
          (retainedSeedSlot r P Q kept hsub hkept (prefixRectangleInput hdiag x)) := hplaced
  have hrow : ∀ x, entry b (LayerPacking.sequenceCell rows x) =
      sortedSeedEndpoint candidates r Q gap hcard
        (retainedSeedSlot r P Q kept hsub hkept (prefixNetworkInput hfit (hrows.trans hrlen) 0 x)) := by
    intro x
    rw [← prefixNetworkInput_cast_comp hfit hrows hrlen 0 x]
    exact hrplaced x
  have hcol : ∀ x, entry b (LayerPacking.sequenceCell cols x).swap =
      sortedSeedEndpoint candidates r Q gap hcard
        (retainedSeedSlot r P Q kept hsub hkept (prefixNetworkInput hfit (hcols.trans hclen) 1 x)) := by
    intro x
    rw [← prefixNetworkInput_cast_comp hfit hcols hclen 1 x]
    exact hcplaced x
  obtain ⟨hcellinj, hused⟩ := prefixPhysicalCells_realizes_retained candidates hcard kept hsub hkept
    hinj hfit hdiag hexact hrect hs choice rows cols (hrows.trans hrlen) (hcols.trans hclen)
    b hrectangle hrow hcol
  exact ⟨rows, cols, hrows, hcols, b, hrmap, hcmap, hrpack, hcpack, hdis,
    hrectangle, hrow, hcol, hrgap, hcgap, hcellinj, hused, hfixed⟩

end
end Sude
