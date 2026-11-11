import Sude.FWJointGraphEndpoints

/-! Recover stage-wise wide graph maps from supplied physical coordinates.
No packing, witness, or placement existence is asserted. -/
namespace Sude
noncomputable section

/-- Pointwise stage-layer endpoint equations determine the entire list of
stage-repeated graph permutations, including the empty-stage case. -/
theorem bridgeStageLayer_maps_of_endpoints {J r n : ℕ}
    (layers : List (LayerPacking.Layer n)) (hlen : layers.length = J * r)
    (perms : Fin r → Equiv.Perm (Fin n))
    (hend : ∀ (j : Fin J) (k : Fin r) (e : Fin n),
      (layers.get (bridgeStageLayerIndex hlen j k)).1 e = perms k e) :
    layers.map Prod.fst = bridgeRepeatedPermutations J perms := by
  apply List.ext_get
  · simpa [hlen] using (bridgeRepeatedPermutations_length (J := J) perms).symm
  · intro i hi hj
    have hi' : i < layers.length := by simpa using hi
    let t : Fin J × Fin r := finProdFinEquiv.symm (Fin.cast hlen ⟨i, hi'⟩)
    have ht : bridgeStageLayerIndex hlen t.1 t.2 = ⟨i, hi'⟩ := by
      change Fin.cast hlen.symm (finProdFinEquiv
        (finProdFinEquiv.symm (Fin.cast hlen ⟨i, hi'⟩))) = ⟨i, hi'⟩
      rw [Equiv.apply_symm_apply, Fin.cast_cast]
      rfl
    apply Equiv.ext
    intro e
    have h := hend t.1 t.2 e
    rw [ht] at h
    simpa [bridgeRepeatedPermutations, t] using h

/-- The supplied same-witness wide row/column coordinate equations force
both family lists to use the common repeated graph permutation triple. -/
theorem fw_wide_graph_maps_of_physical_coordinates {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (wr wc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (p : Fin 3 → Equiv.Perm (Fin n))
    (hcoords : ∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) (side : Bool),
      fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e false side) =
        ((if side then p k e else e), (wr.get (bridgeStageLayerIndex hwr j k)).2 e) ∧
      fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e true side) =
        ((wc.get (bridgeStageLayerIndex hwc j k)).2 e, (if side then p k e else e))) :
    wr.map Prod.fst = bridgeRepeatedPermutations (3 * (n / 450)) p ∧
    wc.map Prod.fst = bridgeRepeatedPermutations (3 * (n / 450)) p := by
  have h := fw_wide_layer_endpoints_of_physical_coordinates hwide hs choice wr wc hwr hwc p hcoords
  exact ⟨bridgeStageLayer_maps_of_endpoints wr hwr p (fun j k e => (h j k e).1),
    bridgeStageLayer_maps_of_endpoints wc hwc p (fun j k e => (h j k e).2)⟩

end
end Sude
