import Sude.NarrowSeedPoolValues
import Sude.VariablePrefixPhysical

/-! Place the retained sorted seed pairs in actual square cells. -/
namespace Sude
noncomputable section

/-- Place a selected seed family in diagonal rectangles and both ordinary
networks, preserving all earlier cells. Supply, permutations, physical
geometry and capacities remain explicit. -/
theorem install_retained_seed_pairs {n r P Q gap d layers L B : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q)
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P)
    (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
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
    let values := retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav
    ∃ (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = rowPerms.length)
      (hcols : cols.length = colPerms.length) (b : Cell n ≃ Fin (n * n)),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers (base ∪ allocatedBridgeRectangleSupport hrect hs choice) rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        ((base ∪ allocatedBridgeRectangleSupport hrect hs choice) ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows) (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ x : Fin (P * (4 * d)) × Fin 4,
        entry b (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
          (values (prefixRectangleInput hdiag x)).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell rows x) =
        (values (prefixNetworkInput hfit hrlen 0 (Fin.cast hrows x.1, x.2))).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell cols x).swap =
        (values (prefixNetworkInput hfit hclen 1 (Fin.cast hcols x.1, x.2))).val) ∧
      (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
        entry b (e, (rows.get i).2 e) + variablePrefixNetworkGap (fun _ => gap) hrlen (Fin.cast hrows i) e) ∧
      (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
        entry b ((cols.get i).2 e, e) + variablePrefixNetworkGap (fun _ => gap) hclen (Fin.cast hcols i) e) ∧
      (∀ c ∈ base, entry b c = entry a c) := by
  dsimp only
  exact install_variable_prefix_diagonal_and_ordinary hfit hdiag hrect hs choice (fun _ => gap)
    (retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav)
    (retainedSeedPoolValues_injective candidates r P Q gap hcard kept hsub hkept initial hav hinj)
    (retainedSeedPoolValues_gap candidates r P Q gap hcard kept hsub hkept initial hav)
    initial (retainedSeedPoolValues_avoid candidates r P Q gap hcard kept hsub hkept initial hav)
    rowPerms colPerms hrlen hclen hrderange hcderange base hrload hcload hcapacity a hbase hfree

end
end Sude
