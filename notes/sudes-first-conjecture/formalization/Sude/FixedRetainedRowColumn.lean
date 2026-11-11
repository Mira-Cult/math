import Sude.PhysicalRowColumnProbability
import Sude.PermutedSeedMidpoints
import Sude.FixedSeedLayout

/-! One probability witness and its realization using actual retained pairs. -/
namespace Sude
noncomputable section

theorem fixed_retained_row_column_allocation {n r P Q gap d layers L : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (hn : 0 < n) (hQ : 0 < Q) (hd : d = 2 * layers) (z : ℝ)
    (hwidth : ∀ j,
      (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩ -
       retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩) ^ 2 ≤ z ^ 2)
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hrows : rows.length = P * layers) (hcols : cols.length = P * layers)
    (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows rows)
    (packedCols : LayerPacking.PackedLayers reservedCols cols)
    (a : Cell n ≃ Fin (n * n)) (base : Finset (Cell n))
    (hbase : ∀ c ∈ base, entry a c ∈ initial)
    (hcells : Function.Injective (prefixPhysicalCells hrect hs choice rows cols hrows hcols))
    (hfree : ∀ x, prefixPhysicalCells hrect hs choice rows cols hrows hcols x ∉ base) :
    ∃ ω : Fin P → Equiv.Perm (Fin Q), ∃ b : Cell n ≃ Fin (n * n),
      (∀ l, |stageLineCentered (physicalRowColumnSlots hfit hdiag)
        (physicalRowColumnWeights hfit hdiag hrect hs choice rows cols hrows hcols)
        (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept) l ω| ≤
        Real.sqrt (((3 * (d : ℝ) * (∑ j,
          (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩ -
           retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩) ^ 2) + 4 * z ^ 2) *
          Real.log (4 * ((n + n : ℕ) : ℝ))) / 2)) ∧
      (∀ x, entry b (prefixPhysicalCells hrect hs choice rows cols hrows hcols x) =
        (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
          (prefixPhysicalInput hfit hdiag x)).val) ∧
      (∀ c ∈ base, entry b c = entry a c) ∧
      Finset.univ.image (fun x => entry b
        (prefixPhysicalCells hrect hs choice rows cols hrows hcols x)) =
          retainedSeedEndpoints candidates r Q gap hcard kept hsub := by
  let values := retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept
  let lo : Fin P → ℝ := fun j => values j ⟨0, hQ⟩
  let upper : Fin P → ℝ := fun j => values j ⟨Q - 1, by omega⟩
  have hvalues : ∀ j k, values j k ∈ Set.Icc (lo j) (upper j) := by
    intro j k
    exact retainedStageMidpoint_bounds candidates r P Q gap hcard kept hsub hkept initial hav hQ j k
  obtain ⟨ω, hbound⟩ := physical_row_column_midpoint_allocation hn hQ hd hfit hdiag hrect hs choice
    rows cols hrows hcols reservedRows reservedCols packedRows packedCols values lo upper z hvalues hwidth
  obtain ⟨b, hb, hfixed, hused⟩ := fixed_seed_layout_accepts_all_permutations
    candidates hcard kept hsub hkept initial hav hinj hfit hdiag hexact hrect hs choice
    rows cols hrows hcols a base hbase hcells hfree ω
  exact ⟨ω, b, hbound, hb, hfixed, hused⟩

end
end Sude
