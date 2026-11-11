import Sude.PhysicalStageInvoice

/-! Derangements inherited by actual bridge and wide stages from their
supplied joint layer packing. No incidence mass or numeric invoice is asserted. -/
namespace Sude
noncomputable section

/-- Every individual layer occurring in a supplied packing has a derangement
as its edge permutation. -/
theorem packed_layer_member_derange {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (LayerPacking.Layer n)} (packed : LayerPacking.PackedLayers reserved layers)
    (layer : LayerPacking.Layer n) (hmem : layer ∈ layers) (i : Fin n) : layer.1 i ≠ i := by
  intro heq
  have hinj := (packed.each_layer layer hmem).1
  have hc : LayerPacking.layerCell layer.1 layer.2 (i, false) =
      LayerPacking.layerCell layer.1 layer.2 (i, true) := by
    change (i, layer.2 i) = (layer.1 i, layer.2 i)
    exact congrArg (fun t => (t, layer.2 i)) heq.symm
  have hfalse : false = true := congrArg Prod.snd (hinj hc)
  cases hfalse

/-- Any stage-indexed list whose layers occur in a joint packing inherits
its derangements without assuming a separate packing of that list. -/
theorem packed_selected_stage_derange {n P K : ℕ} {reserved : Finset (Cell n)}
    {all selected : List (LayerPacking.Layer n)}
    (packed : LayerPacking.PackedLayers reserved all)
    (hsub : ∀ layer, layer ∈ selected → layer ∈ all)
    (hlen : selected.length = P * K) (j : Fin P) (k : Fin K) (i : Fin n) :
    (prefixStageLayer selected hlen j k).1 i ≠ i := by
  apply packed_layer_member_derange packed
  exact hsub _ (List.get_mem selected (Fin.cast hlen.symm (finProdFinEquiv (j,k))))

/-- The bridge and wide row and column stage layers all inherit derangements
from their respective supplied joint packed layer lists. Reservations may
be arbitrary and need not be the same in the two orientations. -/
theorem fw_joint_bridge_wide_stage_derangements {n : ℕ}
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers reservedCols (((bc ++ sc) ++ wc) ++ gc)) :
    (∀ j : Fin 5, ∀ k : Fin 3, ∀ i : Fin n, (prefixStageLayer br hbr j k).1 i ≠ i) ∧
    (∀ j : Fin 5, ∀ k : Fin 3, ∀ i : Fin n, (prefixStageLayer bc hbc j k).1 i ≠ i) ∧
    (∀ j : Fin (3 * (n / 450)), ∀ k : Fin 3, ∀ i : Fin n, (prefixStageLayer wr hwr j k).1 i ≠ i) ∧
    (∀ j : Fin (3 * (n / 450)), ∀ k : Fin 3, ∀ i : Fin n, (prefixStageLayer wc hwc j k).1 i ≠ i) := by
  constructor
  · intro j k i
    apply packed_selected_stage_derange hrows _ hbr j k i
    intro layer hlayer
    simp [hlayer]
  constructor
  · intro j k i
    apply packed_selected_stage_derange hcols _ hbc j k i
    intro layer hlayer
    simp [hlayer]
  constructor
  · intro j k i
    apply packed_selected_stage_derange hrows _ hwr j k i
    intro layer hlayer
    simp [hlayer]
  · intro j k i
    apply packed_selected_stage_derange hcols _ hwc j k i
    intro layer hlayer
    simp [hlayer]

end
end Sude
