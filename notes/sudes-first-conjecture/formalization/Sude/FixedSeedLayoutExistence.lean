import Sude.FixedSeedLayout

/-! The physical geometry can be selected before stage permutations. -/
namespace Sude
noncomputable section

theorem exists_fixed_seed_layout {n r P Q gap d layers L B : ℕ}
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
      (hcols : cols.length = colPerms.length),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers (base ∪ allocatedBridgeRectangleSupport hrect hs choice) rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        ((base ∪ allocatedBridgeRectangleSupport hrect hs choice) ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows) (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      Function.Injective (prefixPhysicalCells hrect hs choice rows cols (hrows.trans hrlen) (hcols.trans hclen)) ∧
      (∀ x, prefixPhysicalCells hrect hs choice rows cols (hrows.trans hrlen) (hcols.trans hclen) x ∉ base) ∧
      ∀ ω : Fin P → Equiv.Perm (Fin Q), ∃ b : Cell n ≃ Fin (n * n),
        (∀ x, entry b (prefixPhysicalCells hrect hs choice rows cols (hrows.trans hrlen) (hcols.trans hclen) x) =
          (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
            (prefixPhysicalInput hfit hdiag x)).val) ∧
        (∀ c ∈ base, entry b c = entry a c) ∧
        Finset.univ.image (fun x => entry b
          (prefixPhysicalCells hrect hs choice rows cols (hrows.trans hrlen) (hcols.trans hclen) x)) =
            retainedSeedEndpoints candidates r Q gap hcard kept hsub := by
  let ω₀ : Fin P → Equiv.Perm (Fin Q) := fun _ => Equiv.refl _
  obtain ⟨rows, cols, hrows, hcols, b₀, hrmap, hcmap, hrpack, hcpack, hdis,
      hrectplace, hrplace, hcplace, hrgap, hcgap, hcell, hused, hfixed⟩ :=
    install_permuted_retained_seed_pairs_exhaustively candidates hcard kept hsub hkept initial hav hinj ω₀
      hfit hdiag hexact hrect hs choice rowPerms colPerms hrlen hclen hrderange hcderange
      base hrload hcload hcapacity a hbase hfree
  have hplace : ∀ x, entry b₀ (prefixPhysicalCells hrect hs choice rows cols
      (hrows.trans hrlen) (hcols.trans hclen) x) =
      (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω₀
        (prefixPhysicalInput hfit hdiag x)).val := by
    intro x
    rcases x with x | (x | x)
    · exact hrectplace x
    · simpa [prefixPhysicalCells, prefixPhysicalInput, prefixNetworkInput] using
        hrplace (Fin.cast (hrows.trans hrlen).symm x.1, x.2)
    · simpa [prefixPhysicalCells, prefixPhysicalInput, prefixNetworkInput] using
        hcplace (Fin.cast (hcols.trans hclen).symm x.1, x.2)
  have hcellfree : ∀ x, prefixPhysicalCells hrect hs choice rows cols
      (hrows.trans hrlen) (hcols.trans hclen) x ∉ base := by
    intro x hx
    have hn := permutedRetainedSeedValues_avoid candidates r P Q gap hcard kept hsub hkept initial hav ω₀
      (prefixPhysicalInput hfit hdiag x)
    rw [← hplace x, hfixed _ hx] at hn
    exact hn (hbase _ hx)
  refine ⟨rows, cols, hrows, hcols, hrmap, hcmap, hrpack, hcpack, hdis, hcell, hcellfree, ?_⟩
  exact fixed_seed_layout_accepts_all_permutations candidates hcard kept hsub hkept initial hav hinj
    hfit hdiag hexact hrect hs choice rows cols (hrows.trans hrlen) (hcols.trans hclen)
    a base hbase hcell hcellfree

end
end Sude
