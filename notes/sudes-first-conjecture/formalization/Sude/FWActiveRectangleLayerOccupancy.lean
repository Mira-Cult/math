import Sude.FWActiveRectangleLabels
import Sude.ActiveRectangleLayerOccupancy

/-! Conditional occupancy of the supplied FW active rectangle labels and
normalized packed layers. This does not construct an FW witness. -/
namespace Sude
noncomputable section

/-- The support selected by these active labels and supplied layer sequences. -/
def fwActiveRectangleLayerSupport {n P : ℕ} (hP : P ≤ 238)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (rows cols : List (LayerPacking.Layer n)) : Finset (Cell n) :=
  activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) ∪
    LayerPacking.layersSupport rows ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport cols)

/-- If each orientation supplies three packed layers per active stage and the
three supplied supports are pairwise disjoint, their union has the stated
cardinality and line counts. The geometric assumptions remain explicit. -/
theorem fw_active_rectangle_layer_occupancy {n P : ℕ} (hP : P ≤ 238)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (rowReserved colReserved : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers rowReserved rows)
    (hcols : LayerPacking.PackedLayers colReserved cols)
    (hrowLength : rows.length = 3 * (5 + 16 + 3 * (n / 450) + P))
    (hcolLength : cols.length = 3 * (5 + 16 + 3 * (n / 450) + P))
    (hrectRow : Disjoint (activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP))
      (LayerPacking.layersSupport rows))
    (hrectCol : Disjoint (activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP))
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)))
    (hrowCol : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols))) :
    let S := 5 + 16 + 3 * (n / 450) + P
    let total := fwActiveRectangleLayerSupport hP hs choice rows cols
    total.card = 12 * S * (n + 8) ∧
    (∀ r, (LayerPacking.rowUsed total r).card =
      (LayerPacking.rowUsed (activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)) r).card + 12 * S) ∧
    (∀ c, (LayerPacking.colUsed total c).card =
      (LayerPacking.colUsed (activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)) c).card + 12 * S) ∧
    (∀ r, (LayerPacking.rowUsed total r).card = 12 * S ∨
      (LayerPacking.rowUsed total r).card = 12 * S + 2) ∧
    (∀ c, (LayerPacking.colUsed total c).card = 12 * S ∨
      (LayerPacking.colUsed total c).card = 12 * S + 2) := by
  classical
  dsimp only
  have h := active_rectangle_packed_layer_occupancy hs choice (fwActiveRectangleLabels n P hP)
    rows cols rowReserved colReserved hrows hcols hrectRow hrectCol hrowCol
  dsimp only at h
  rw [fw_active_rectangle_label_count, hrowLength, hcolLength] at h
  change (activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) ∪
    LayerPacking.layersSupport rows ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport cols)).card = _ ∧ _
  constructor
  · calc
      _ = 4 * (24 * (5 + 16 + 3 * (n / 450) + P)) +
          2 * n * (3 * (5 + 16 + 3 * (n / 450) + P) +
            3 * (5 + 16 + 3 * (n / 450) + P)) := h.1
      _ = _ := by ring
  · constructor
    · intro r
      have hr := h.2.1 r
      dsimp [fwActiveRectangleLayerSupport]
      omega
    · constructor
      · intro c
        have hc := h.2.2.1 c
        dsimp [fwActiveRectangleLayerSupport]
        omega
      · constructor
        · intro r
          have hr := h.2.2.2.1 r
          dsimp [fwActiveRectangleLayerSupport]
          rcases hr with hr | hr <;> omega
        · intro c
          have hc := h.2.2.2.2 c
          dsimp [fwActiveRectangleLayerSupport]
          rcases hc with hc | hc <;> omega

end
end Sude
