import Sude.FWBridgeWidePairPlacement
import Sude.StageDoubleBlockReallocation

/-! Regroup existing bridge and wide physical pair slots into the input of
stage-wise double-block reallocation. Geometry is supplied; no new placement,
protected-support disjointness, concentration, or grid property is asserted. -/

namespace Sude
noncomputable section

/-- Regroup the two oriented pairs belonging to each source double block. -/
def fwBlockPairIndex (P n : ℕ) :
    ((Fin P × Fin (3 * (n + 8)) × Fin 2) × Bool) ≃
      ((Fin P × Fin (6 * (n + 8))) × Bool) where
  toFun x := ((x.1.1, Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8))
    (finProdFinEquiv (x.1.2.1, x.1.2.2))), x.2)
  invFun x :=
    let t := finProdFinEquiv.symm
      (Fin.cast (by omega : 6 * (n + 8) = 3 * (n + 8) * 2) x.1.2)
    ((x.1.1, t.1, t.2), x.2)
  left_inv := by
    rintro ⟨⟨j,b,p⟩,side⟩
    simp only [Fin.cast_cast, Fin.cast_refl, id_eq, Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨j,i⟩,side⟩
    simp only [Fin.cast_cast, Fin.cast_refl, id_eq, Equiv.apply_symm_apply, Prod.eta]


/-- The regrouping selects the original double block and keeps the two
oriented corner pairs, including the reversed second pair. -/
theorem fw_grouped_controller_slot (P n : ℕ) (j : Fin P)
    (b : Fin (3 * (n + 8))) (p : Fin 2) (side : Bool) :
    fwPairControllerEquiv P n (fwBlockPairIndex P n ((j, b, p), side)) =
      ((j, b), prefixPairCorner p side) := by
  exact fw_pair_controller_slot P n j b p side

/-- The existing bridge pair cells, indexed by stage, block and pair. -/
def fwBridgePhysicalDoubleCells {n L : ℕ} (hrect : 5 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3) :
    ((Fin 5 × Fin (3 * (n + 8)) × Fin 2) × Bool) → Cell n :=
  fwBridgePhysicalPairCells hrect hs choice rows cols hr hc ∘ fwBlockPairIndex 5 n

/-- The existing wide pair cells, indexed by stage, block and pair. -/
def fwWidePhysicalDoubleCells {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = (3 * (n / 450)) * 3)
    (hc : cols.length = (3 * (n / 450)) * 3) :
    ((Fin (3 * (n / 450)) × Fin (3 * (n + 8)) × Fin 2) × Bool) → Cell n :=
  fwWidePhysicalPairCells hwide hs choice rows cols hr hc ∘ fwBlockPairIndex (3 * (n / 450)) n

/-- A bijective regrouping preserves physical injectivity and full support. -/
theorem fw_double_cells_geometry {P n : ℕ}
    (cells : ((Fin P × Fin (6 * (n + 8))) × Bool) → Cell n)
    (hinj : Function.Injective cells) :
    Function.Injective (cells ∘ fwBlockPairIndex P n) ∧
      Finset.univ.image (cells ∘ fwBlockPairIndex P n) = Finset.univ.image cells := by
  constructor
  · exact hinj.comp (fwBlockPairIndex P n).injective
  · rw [← Finset.image_image, Finset.image_univ_of_surjective (fwBlockPairIndex P n).surjective]


/-- Grouping the supplied bridge pairs is injective and retains both the
rectangle and ordinary-layer slot images. -/
theorem fw_bridge_double_cells_geometry {n L : ℕ} (hrect : 5 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (hinj : Function.Injective (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc)) :
    Function.Injective (fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc) ∧
      Finset.univ.image (fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc) =
        Finset.univ.image (fun x : Fin (5 * (4 * 6)) × Fin 4 =>
          packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect x.1, x.2)) ∪
        Finset.univ.image (fwBridgeLayerCells rows cols hr hc) := by
  obtain ⟨hi, hsupp⟩ := fw_double_cells_geometry (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc) hinj
  exact ⟨hi, hsupp.trans (fw_bridge_physical_pair_cells_image hrect hs choice rows cols hr hc)⟩

/-- Grouping the supplied wide pairs is injective and retains the complete
wide-role image, including the diagonal rectangles. -/
theorem fw_wide_double_cells_geometry {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = (3 * (n / 450)) * 3)
    (hc : cols.length = (3 * (n / 450)) * 3)
    (hinj : Function.Injective (fwWidePhysicalPairCells hwide hs choice rows cols hr hc)) :
    Function.Injective (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc) ∧
      Finset.univ.image (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc) =
        Finset.univ.image (fwWidePhysicalCells hwide hs choice rows cols hr hc) := by
  obtain ⟨hi, hsupp⟩ := fw_double_cells_geometry (fwWidePhysicalPairCells hwide hs choice rows cols hr hc) hinj
  exact ⟨hi, hsupp.trans (fw_wide_physical_pair_cells_image hwide hs choice rows cols hr hc)⟩

end
end Sude
