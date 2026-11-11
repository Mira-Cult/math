import Sude.PrefixPhysicalLineSum
import Sude.PhysicalSlotInvoice

/-! Identify each probability slot with its actual physical prefix cells. -/
namespace Sude
noncomputable section

/-- Exact capacity makes the injective physical pair-slot map bijective. -/
theorem prefixStagePairSlot_bijective {d layers n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q) :
    Function.Bijective (prefixStagePairSlot hfit hdiag) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨prefixStagePairSlot_injective hfit hdiag, ?_⟩
  simp only [PrefixStagePair, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [← hexact]

/-- Every allocator pair slot has exactly one physical prefix label. -/
theorem physicalPrefixSlots_eq_univ {d layers n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q) :
    physicalPrefixSlots hfit hdiag = Finset.univ := by
  exact Finset.image_univ_of_surjective (prefixStagePairSlot_bijective hfit hdiag hexact).2

/-- The rectangle pair slot's two reindexed cells are exactly the actual
packed rectangle corners, with the second pair's orientation retained. -/
theorem prefixPairCells_rectangle {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (rect : Fin (4 * d))
    (pair : Fin 2) (side : Bool) :
    prefixPairCells hfit hdiag hexact hrect hs choice rows cols hrows hcols
      ((j, prefixDiagonalPairIndex hdiag (rect, pair)), side) =
    packedRectangleCorner hs choice (Fin.castLE hrect (finProdFinEquiv (j, rect)), prefixPairCorner pair side) := by
  have he : (prefixPhysicalInputEquiv (P := P) hfit hdiag hexact).symm
      ((j, prefixDiagonalPairIndex hdiag (rect, pair)), side) =
      Sum.inl (finProdFinEquiv (j, rect), prefixPairCorner pair side) := by
    apply (prefixPhysicalInputEquiv (P := P) hfit hdiag hexact).symm_apply_eq.mpr
    simpa [prefixPhysicalInputEquiv, prefixPhysicalInput] using
      (prefixRectangleInput_pair hdiag j rect pair side).symm
  simp only [prefixPairCells, he, prefixPhysicalCells]

/-- A row-network pair slot names the corresponding two actual row-layer cells. -/
theorem prefixPairCells_row_network {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (k : Fin layers) (edge : Fin n) (side : Bool) :
    prefixPairCells hfit hdiag hexact hrect hs choice rows cols hrows hcols
      ((j, prefixOrdinaryPairIndex hfit (0, k, edge)), side) =
    LayerPacking.sequenceCell rows (Fin.cast hrows.symm (finProdFinEquiv (j, k)), (edge, side)) := by
  have he : (prefixPhysicalInputEquiv (P := P) hfit hdiag hexact).symm
      ((j, prefixOrdinaryPairIndex hfit (0, k, edge)), side) =
      Sum.inr (Sum.inl (finProdFinEquiv (j, k), (edge, side))) := by
    apply (prefixPhysicalInputEquiv (P := P) hfit hdiag hexact).symm_apply_eq.mpr
    simpa [prefixPhysicalInputEquiv, prefixPhysicalInput] using
      (prefixStageLayer_networkInput hfit rfl 0 j k edge side).symm
  simp only [prefixPairCells, he, prefixPhysicalCells]

/-- A column-network pair slot names the transposed actual column-layer cells. -/
theorem prefixPairCells_column_network {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (k : Fin layers) (edge : Fin n) (side : Bool) :
    prefixPairCells hfit hdiag hexact hrect hs choice rows cols hrows hcols
      ((j, prefixOrdinaryPairIndex hfit (1, k, edge)), side) =
    (LayerPacking.sequenceCell cols (Fin.cast hcols.symm (finProdFinEquiv (j, k)), (edge, side))).swap := by
  have he : (prefixPhysicalInputEquiv (P := P) hfit hdiag hexact).symm
      ((j, prefixOrdinaryPairIndex hfit (1, k, edge)), side) =
      Sum.inr (Sum.inr (finProdFinEquiv (j, k), (edge, side))) := by
    apply (prefixPhysicalInputEquiv (P := P) hfit hdiag hexact).symm_apply_eq.mpr
    simpa [prefixPhysicalInputEquiv, prefixPhysicalInput] using
      (prefixStageLayer_networkInput hfit rfl 1 j k edge side).symm
  simp only [prefixPairCells, he, prefixPhysicalCells]

end
end Sude
