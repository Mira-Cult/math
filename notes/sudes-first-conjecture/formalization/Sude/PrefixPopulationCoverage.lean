import Sude.PrefixInstalledNetwork

/-! Every retained FPF endpoint is allocated to exactly one physical family. -/
namespace Sude
noncomputable section

def prefixAllInput {P d r n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q) :
    Sum (Fin (P * (4 * d)) × Fin 4)
      ((Fin P × (Fin 2 × (Fin r × Fin n))) × Bool) → (Fin P × Fin Q) × Bool :=
  Sum.elim (prefixRectangleInput hdiag) (prefixOrdinaryInput hfit)

theorem prefixAllInput_injective {P d r n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q) :
    Function.Injective (prefixAllInput (P := P) hfit hdiag) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (prefixRectangleInput_injective hdiag h)
    | inr b => exact False.elim (prefixOrdinaryInput_ne_rectangle hfit hdiag b a h.symm)
  | inr a =>
    cases b with
    | inl b => exact False.elim (prefixOrdinaryInput_ne_rectangle hfit hdiag a b h)
    | inr b => exact congrArg Sum.inr (prefixOrdinaryInput_injective hfit h)

/-- With the source's exact pair count, the diagonal and ordinary families
exhaust every retained endpoint, not merely a subset of the population. -/
theorem prefixAllInput_bijective {P d r n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (r * n) = Q) :
    Function.Bijective (prefixAllInput (P := P) hfit hdiag) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨prefixAllInput_injective hfit hdiag, ?_⟩
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  nlinarith [hexact]

theorem prefixNetworkInput_stage {P d r n Q m : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hlen : m = P * r)
    (j : Fin P) (network : Fin 2) (layer : Fin r) (edge : Fin n) (side : Bool) :
    prefixNetworkInput hfit hlen network (bridgeStageLayerIndex hlen j layer, (edge, side)) =
      prefixOrdinaryInput hfit ((j, (network, (layer, edge))), side) := by
  simp [prefixNetworkInput, bridgeStageLayerIndex]

/-- Once the three physical families are installed, each original retained
endpoint occurs in one of their actual cells. This is the reservation invariant
needed before later bridge and wide-pair selections. -/
theorem installed_prefix_covers_population {P d r n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (r * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (values : (Fin P × Fin Q) × Bool → pool n) (a : Cell n ≃ Fin (n * n))
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = P * r) (hclen : colPerms.length = P * r)
    (rows cols : List (LayerPacking.Layer n))
    (hrows : rows.length = rowPerms.length) (hcols : cols.length = colPerms.length)
    (hdiagPlaced : ∀ x : Fin (P * (4 * d)) × Fin 4,
      entry a (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
        (values (prefixRectangleInput hdiag x)).val)
    (hrowPlaced : ∀ x, entry a (LayerPacking.sequenceCell rows x) =
      (values (prefixNetworkInput hfit hrlen 0 (Fin.cast hrows x.1, x.2))).val)
    (hcolPlaced : ∀ x, entry a (LayerPacking.sequenceCell cols x).swap =
      (values (prefixNetworkInput hfit hclen 1 (Fin.cast hcols x.1, x.2))).val) :
    ∀ x : (Fin P × Fin Q) × Bool, ∃ c ∈
      allocatedBridgeRectangleSupport hrect hs choice ∪
        (LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)),
      entry a c = (values x).val := by
  intro x
  obtain ⟨u, hu⟩ := (prefixAllInput_bijective hfit hdiag hexact).2 x
  cases u with
  | inl u =>
    refine ⟨packedRectangleCorner hs choice (Fin.castLE hrect u.1, u.2), ?_, ?_⟩
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨u, Finset.mem_univ _, rfl⟩
    · rw [hdiagPlaced]
      exact congrArg (fun z => (values z).val) hu
  | inr u =>
    rcases u with ⟨⟨j, network, layer, edge⟩, side⟩
    fin_cases network
    · let i := bridgeStageLayerIndex hrlen j layer
      let z : Fin rows.length × (Fin n × Bool) := (Fin.cast hrows.symm i, (edge, side))
      refine ⟨LayerPacking.sequenceCell rows z, ?_, ?_⟩
      · apply Finset.mem_union_right
        apply Finset.mem_union_left
        exact LayerPacking.layerSupport_subset (rows.get z.1) rows (List.get_mem rows z.1)
          (LayerPacking.sequenceCell_mem rows z.1 z.2)
      · rw [hrowPlaced]
        have hi : Fin.cast hrows z.1 = i := by simp [z]
        rw [hi, prefixNetworkInput_stage]
        exact congrArg (fun z => (values z).val) hu
    · let i := bridgeStageLayerIndex hclen j layer
      let z : Fin cols.length × (Fin n × Bool) := (Fin.cast hcols.symm i, (edge, side))
      refine ⟨(LayerPacking.sequenceCell cols z).swap, ?_, ?_⟩
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        exact ⟨LayerPacking.sequenceCell cols z,
          LayerPacking.layerSupport_subset (cols.get z.1) cols (List.get_mem cols z.1)
            (LayerPacking.sequenceCell_mem cols z.1 z.2), rfl⟩
      · rw [hcolPlaced]
        have hi : Fin.cast hcols z.1 = i := by simp [z]
        rw [hi, prefixNetworkInput_stage]
        exact congrArg (fun z => (values z).val) hu

/-- The values in the three installed cell families are exactly the full
retained prefix population. This equality can be used as the explicit
deletion set for every later stock calculation. -/
theorem installed_prefix_population_exact {P d r n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (r * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (values : (Fin P × Fin Q) × Bool → pool n) (a : Cell n ≃ Fin (n * n))
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = P * r) (hclen : colPerms.length = P * r)
    (rows cols : List (LayerPacking.Layer n))
    (hrows : rows.length = rowPerms.length) (hcols : cols.length = colPerms.length)
    (hdiagPlaced : ∀ x : Fin (P * (4 * d)) × Fin 4,
      entry a (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
        (values (prefixRectangleInput hdiag x)).val)
    (hrowPlaced : ∀ x, entry a (LayerPacking.sequenceCell rows x) =
      (values (prefixNetworkInput hfit hrlen 0 (Fin.cast hrows x.1, x.2))).val)
    (hcolPlaced : ∀ x, entry a (LayerPacking.sequenceCell cols x).swap =
      (values (prefixNetworkInput hfit hclen 1 (Fin.cast hcols x.1, x.2))).val) :
    (allocatedBridgeRectangleSupport hrect hs choice ∪
      (LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols))).image
        (entry a) = (Finset.univ : Finset ((Fin P × Fin Q) × Bool)).image (fun x => (values x).val) := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rcases Finset.mem_union.mp hc with hc | hc
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc
      exact ⟨prefixRectangleInput hdiag x, (hdiagPlaced x).symm⟩
    · rcases Finset.mem_union.mp hc with hc | hc
      · obtain ⟨x, rfl⟩ := LayerPacking.sequenceCell_covers rows c hc
        exact ⟨prefixNetworkInput hfit hrlen 0 (Fin.cast hrows x.1, x.2), (hrowPlaced x).symm⟩
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨x, rfl⟩ := LayerPacking.sequenceCell_covers cols z hz
        exact ⟨prefixNetworkInput hfit hclen 1 (Fin.cast hcols x.1, x.2), (hcolPlaced x).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨c, hc, heq⟩ := installed_prefix_covers_population hfit hdiag hexact hrect hs choice
      values a rowPerms colPerms hrlen hclen rows cols hrows hcols hdiagPlaced hrowPlaced hcolPlaced x
    exact ⟨c, hc, heq⟩

/-- The retained deletion budget counts both endpoints of every one of the
Q pairs in every stage; injectivity prevents double counting. -/
theorem prefixPopulation_card {P Q n : ℕ} (values : (Fin P × Fin Q) × Bool → pool n)
    (hinj : Function.Injective values) :
    ((Finset.univ : Finset ((Fin P × Fin Q) × Bool)).image (fun x => (values x).val)).card =
      2 * Q * P := by
  have hv : Function.Injective (fun x => (values x).val) := by
    intro x y h
    exact hinj (Subtype.ext h)
  rw [Finset.card_image_of_injective _ hv]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

end
end Sude
