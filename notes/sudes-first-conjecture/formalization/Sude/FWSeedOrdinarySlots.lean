import Sude.FWSeedLayerPacking
import Sude.PrefixAllocationCoverage

/-! FW's retained seed pair-slot allocation and the ordinary physical
layer cells. No seed values are installed here. -/
namespace Sude
noncomputable section

/-- All ordinary seed roles, indexed by stage-layer, graph edge and side;
the two summands are the row and column networks. -/
abbrev FWSeedOrdinaryInputs (n : ℕ) :=
  (Fin (16 * 3) × (Fin n × Bool)) ⊕ (Fin (16 * 3) × (Fin n × Bool))

/-- The source's exact ordinary pair-slot allocation, disjoint from the
rectangle pair slots. -/
def fwSeedOrdinaryInput (n : ℕ) : FWSeedOrdinaryInputs n →
    (Fin 16 × Fin (6 * (n + 8))) × Bool
  | Sum.inl x => prefixNetworkInput (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) rfl 0 x
  | Sum.inr x => prefixNetworkInput (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) rfl 1 x

theorem fwSeedOrdinaryInput_injective (n : ℕ) : Function.Injective (fwSeedOrdinaryInput n) := by
  intro x y h
  have hreindex (z : FWSeedOrdinaryInputs n) : fwSeedOrdinaryInput n z =
      prefixPhysicalInput (P := 16)
        (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (Sum.inr z) := by
    cases z <;> rfl
  rw [hreindex x, hreindex y] at h
  apply Sum.inr_injective
  apply prefixPhysicalInput_injective
    (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
    (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega)
  exact h

/-- No ordinary seed pair role coincides with any seed rectangle role. -/
theorem fwSeedOrdinaryInput_ne_rectangle (n : ℕ) (x : FWSeedOrdinaryInputs n)
    (y : Fin (16 * (4 * 6)) × Fin 4) :
    fwSeedOrdinaryInput n x ≠ prefixRectangleInput
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) y := by
  intro h
  have hreindex : fwSeedOrdinaryInput n x = prefixPhysicalInput (P := 16)
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (Sum.inr x) := by
    cases x <;> rfl
  rw [hreindex] at h
  have heq := prefixPhysicalInput_injective
    (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
    (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega)
    (show prefixPhysicalInput (P := 16)
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (Sum.inr x) =
      prefixPhysicalInput (P := 16)
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (Sum.inl y) from h)
  cases heq

/-- The complete source allocation (seed rectangles, row network, column
network) uses every retained stage endpoint exactly once. -/
theorem fwSeedPhysicalInput_bijective (n : ℕ) :
    Function.Bijective (prefixPhysicalInput (P := 16)
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega)) := by
  apply prefixPhysicalInput_bijective
  omega

/-- Actual ordinary cells, with column layers returned to original square
coordinates. -/
def fwSeedOrdinaryCells {n : ℕ} (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = 16 * 3) (hc : cols.length = 16 * 3) :
    FWSeedOrdinaryInputs n → Cell n
  | Sum.inl x => LayerPacking.sequenceCell rows (Fin.cast hr.symm x.1, x.2)
  | Sum.inr x => (LayerPacking.sequenceCell cols (Fin.cast hc.symm x.1, x.2)).swap

/-- Supplied packed layers and disjoint supports produce injective ordinary
seed cells. Every such cell avoids the entire earlier physical reservation,
including every joint RP1 rectangle when its support is contained in `base`. -/
theorem fwSeedOrdinaryCells_geometry {n L : ℕ}
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) (base : Finset (Cell n))
    (hrectbase : packedRectangleSupport hs choice ⊆ base)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 16 * 3)
    (hc : cols.length = 16 * 3)
    (hrows : LayerPacking.PackedLayers base rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (base ∪ LayerPacking.layersSupport rows)) cols)
    (hdisjoint : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols))) :
    Function.Injective (fwSeedOrdinaryCells rows cols hr hc) ∧
    (∀ x, fwSeedOrdinaryCells rows cols hr hc x ∉ base) ∧
    (∀ x (t : Fin L) side, fwSeedOrdinaryCells rows cols hr hc x ≠
      packedRectangleCorner hs choice (t, side)) := by
  have hrmem : ∀ x, LayerPacking.sequenceCell rows x ∈ LayerPacking.layersSupport rows := by
    intro x
    exact LayerPacking.layerSupport_subset (rows.get x.1) rows (List.get_mem rows x.1)
      (LayerPacking.sequenceCell_mem rows x.1 x.2)
  have hcmem : ∀ x, (LayerPacking.sequenceCell cols x).swap ∈
      LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
    intro x
    exact Finset.mem_image.mpr ⟨_, LayerPacking.layerSupport_subset (cols.get x.1) cols
      (List.get_mem cols x.1) (LayerPacking.sequenceCell_mem cols x.1 x.2), rfl⟩
  have hinj : Function.Injective (fwSeedOrdinaryCells rows cols hr hc) := by
    intro x y heq
    rcases x with x | x <;> rcases y with y | y <;> dsimp only [fwSeedOrdinaryCells] at heq
    · apply congrArg Sum.inl
      have h := hrows.sequenceCell_injective heq
      exact Prod.ext (Fin.cast_injective hr.symm (congrArg Prod.fst h)) (congrArg (fun z : Fin rows.length × (Fin n × Bool) => z.2) h)
    · exact False.elim (Finset.disjoint_left.mp hdisjoint (hrmem _) (heq ▸ hcmem _))
    · exact False.elim (Finset.disjoint_left.mp hdisjoint (heq ▸ hrmem _) (hcmem _))
    · apply congrArg Sum.inr
      have heq' := congrArg Prod.swap heq
      simp only [Prod.swap_swap] at heq'
      have h := hcols.sequenceCell_injective heq'
      exact Prod.ext (Fin.cast_injective hc.symm (congrArg Prod.fst h)) (congrArg (fun z : Fin cols.length × (Fin n × Bool) => z.2) h)
  have hfree : ∀ x, fwSeedOrdinaryCells rows cols hr hc x ∉ base := by
    intro x
    rcases x with x | x
    · exact hrows.sequenceCell_unreserved _
    · intro hz
      exact (hcols.transposed_support_safe _ (hcmem _)).1 (Finset.mem_union_left _ hz)
  refine ⟨hinj, hfree, ?_⟩
  intro x t side heq
  apply hfree x
  rw [heq]
  exact hrectbase (Finset.mem_image.mpr ⟨(t, side), Finset.mem_univ _, rfl⟩)

end
end Sude
