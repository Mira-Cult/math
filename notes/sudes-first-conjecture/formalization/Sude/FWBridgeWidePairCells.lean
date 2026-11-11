import Sude.FWBridgeRoleValueCoverage
import Sude.FWWidePhysicalSlots
import Sude.RectanglePairInvoice
namespace Sude
noncomputable section

def fwPairControllerEquiv (J n : ℕ) :
    ((Fin J × Fin (6 * (n + 8))) × Bool) ≃ ((Fin J × Fin (3 * (n + 8))) × Fin 4) where
  toFun x :=
    let t := (rectanglePairCornerEquiv (3 * (n + 8)))
      ((finProdFinEquiv.symm (Fin.cast (by omega : 6 * (n + 8) = 3 * (n + 8) * 2) x.1.2)), x.2)
    ((x.1.1, t.1), t.2)
  invFun x :=
    let t := (rectanglePairCornerEquiv (3 * (n + 8))).symm (x.1.2, x.2)
    ((x.1.1, Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8)) (finProdFinEquiv t.1)), t.2)
  left_inv := by
    rintro ⟨⟨j, i⟩, s⟩
    simp only [Prod.eta, id_eq, Equiv.symm_apply_apply, Equiv.apply_symm_apply, Fin.cast_cast, Fin.cast_refl]
  right_inv := by
    rintro ⟨⟨j, i⟩, s⟩
    simp only [Prod.eta, id_eq, Equiv.symm_apply_apply, Equiv.apply_symm_apply, Fin.cast_cast, Fin.cast_refl]

/-- Reindexing keeps the original stage and double block, and uses the
existing oriented corner pair within that block. -/
theorem fw_pair_controller_slot (J n : ℕ) (j : Fin J) (k : Fin (3 * (n + 8)))
    (p : Fin 2) (side : Bool) :
    fwPairControllerEquiv J n
      ((j, Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8))
        (finProdFinEquiv (k, p))), side) = ((j, k), prefixPairCorner p side) := by
  simp only [fwPairControllerEquiv, Equiv.coe_fn_mk, Fin.cast_cast, Fin.cast_refl,
    id_eq, Equiv.symm_apply_apply, rectanglePairCornerEquiv]

/-- The two controller pairs have endpoint orientations (0, 1) and (3, 2). -/
theorem fw_pair_controller_corners :
    prefixPairCorner 0 false = 0 ∧ prefixPairCorner 0 true = 1 ∧
    prefixPairCorner 1 false = 3 ∧ prefixPairCorner 1 true = 2 := by
  decide

/-- The physical bridge map has the existing diagonal-corner and ordinary-layer roles. -/
def fwBridgePhysicalCells {n L : ℕ} (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3) :
    (Fin (5 * (4 * 6)) × Fin 4) ⊕ ((Fin 5 × (Fin 3 × Fin n)) × (Bool × Bool)) → Cell n :=
  Sum.elim (fun x => packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect x.1, x.2))
    (fwBridgeLayerCells rows cols hr hc)

/-- Reindex a pair endpoint using the actual bridge controller-slot bijection. -/
def fwBridgePairCellEquiv (n : ℕ) := (fwPairControllerEquiv 5 n).trans
  (Equiv.ofBijective (fwBridgeControllerSlot n) (fwBridgeControllerSlot_bijective n)).symm

/-- Reindex a pair endpoint using the actual wide controller-slot bijection. -/
def fwWidePairCellEquiv (n : ℕ) := (fwPairControllerEquiv (3 * (n / 450)) n).trans
  (Equiv.ofBijective (fwWideControllerSlot n) (fwWideControllerSlot_bijective n)).symm

/-- The bridge pair-cell map on the supplied rectangle choice and layers. -/
def fwBridgePhysicalPairCells {n L : ℕ} (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3) :
    ((Fin 5 × Fin (6 * (n + 8))) × Bool) → Cell n :=
  fun x => fwBridgePhysicalCells hrect hs choice rows cols hr hc (fwBridgePairCellEquiv n x)

/-- The wide pair-cell map on the supplied rectangle choice and layers. -/
def fwWidePhysicalPairCells {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3) :
    ((Fin (3 * (n / 450)) × Fin (6 * (n + 8))) × Bool) → Cell n :=
  fun x => fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWidePairCellEquiv n x)

/-- The bridge pair cells cover exactly the existing bridge role images. -/
theorem fw_bridge_physical_pair_cells_image {n L : ℕ} (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3) :
    Finset.univ.image (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc) =
      Finset.univ.image (fun x : Fin (5 * (4 * 6)) × Fin 4 =>
        packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect x.1, x.2)) ∪
      Finset.univ.image (fwBridgeLayerCells rows cols hr hc) := by
  classical
  change Finset.univ.image ((fwBridgePhysicalCells hrect hs choice rows cols hr hc) ∘ fwBridgePairCellEquiv n) = _
  rw [← Finset.image_image, Finset.image_univ_of_surjective (fwBridgePairCellEquiv n).surjective]
  ext c
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨x, hx⟩
    cases x with
    | inl x => exact Or.inl ⟨x, hx⟩
    | inr x => exact Or.inr ⟨x, hx⟩
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr x, hx⟩

/-- The wide pair cells cover exactly the existing wide role image. -/
theorem fw_wide_physical_pair_cells_image {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3) :
    Finset.univ.image (fwWidePhysicalPairCells hwide hs choice rows cols hr hc) =
      Finset.univ.image (fwWidePhysicalCells hwide hs choice rows cols hr hc) := by
  classical
  change Finset.univ.image ((fwWidePhysicalCells hwide hs choice rows cols hr hc) ∘ fwWidePairCellEquiv n) = _
  rw [← Finset.image_image, Finset.image_univ_of_surjective (fwWidePairCellEquiv n).surjective]

end
end Sude
