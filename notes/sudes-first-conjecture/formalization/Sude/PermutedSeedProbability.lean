import Sude.PermutedSeedMidpoints
import Sude.StageSquaredInvoice

/-! A common random permutation witness and its physical realization.
The weighted forms and their invoice are explicit hypotheses; identifying
them with square-line contributions remains a separate obligation. -/
namespace Sude
noncomputable section

theorem exists_permuted_retained_seed_pairs_with_weighted_budget {n r P Q gap d layers L B : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q)
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P)
    (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (hQ : 0 < Q) (m : ℕ) (hm : 0 < m)
    (slots : Fin m → Fin P → Finset (Fin Q))
    (weights : Fin m → Fin P → Fin Q → ℝ)
    (V : ℝ) (hV : 0 ≤ V)
    (hnonneg : ∀ l j k, k ∈ slots l j → 0 ≤ weights l j k)
    (hinvoice : ∀ l, (∑ j,
      (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩ -
       retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩) ^ 2 *
      ∑ k ∈ slots l j, (weights l j k) ^ 2) ≤ V)
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
    ∃ ω : Fin P → Equiv.Perm (Fin Q),
      (∀ l, |stageLineCentered slots weights
        (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept) l ω| ≤
        Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2)) ∧
    ∃ (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = rowPerms.length)
      (hcols : cols.length = colPerms.length) (b : Cell n ≃ Fin (n * n)),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers (base ∪ allocatedBridgeRectangleSupport hrect hs choice) rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        ((base ∪ allocatedBridgeRectangleSupport hrect hs choice) ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows) (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ x : Fin (P * (4 * d)) × Fin 4,
        entry b (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
          (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
          (prefixRectangleInput hdiag x)).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell rows x) =
        (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
          (prefixNetworkInput hfit (hrows.trans hrlen) 0 x)).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell cols x).swap =
        (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
          (prefixNetworkInput hfit (hcols.trans hclen) 1 x)).val) ∧
      (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
        entry b (e, (rows.get i).2 e) + variablePrefixNetworkGap (fun _ => gap) hrlen (Fin.cast hrows i) e) ∧
      (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
        entry b ((cols.get i).2 e, e) + variablePrefixNetworkGap (fun _ => gap) hclen (Fin.cast hcols i) e) ∧
      Function.Injective (prefixPhysicalCells hrect hs choice rows cols (hrows.trans hrlen) (hcols.trans hclen)) ∧
      Finset.univ.image (fun x => entry b
        (prefixPhysicalCells hrect hs choice rows cols (hrows.trans hrlen) (hcols.trans hclen) x)) =
          retainedSeedEndpoints candidates r Q gap hcard kept hsub ∧
      ∀ c ∈ base, entry b c = entry a c := by
  let values := retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept
  let lo : Fin P → ℝ := fun j => values j ⟨0, hQ⟩
  let upper : Fin P → ℝ := fun j => values j ⟨Q - 1, by omega⟩
  have hvalues : ∀ j k, values j k ∈ Set.Icc (lo j) (upper j) := by
    intro j k
    exact retainedStageMidpoint_bounds candidates r P Q gap hcard kept hsub hkept initial hav hQ j k
  have hlu : ∀ j, lo j ≤ upper j := by
    intro j
    exact (hvalues j ⟨0, hQ⟩).2
  obtain ⟨ω, hbound⟩ := stageLines_exists_of_squared_invoice hm slots weights values lo upper V hV
    hlu hnonneg hvalues hinvoice
  refine ⟨ω, hbound, ?_⟩
  exact install_permuted_retained_seed_pairs_exhaustively candidates hcard kept hsub hkept initial hav hinj ω
    hfit hdiag hexact hrect hs choice rowPerms colPerms hrlen hclen hrderange hcderange
    base hrload hcload hcapacity a hbase hfree

end
end Sude
