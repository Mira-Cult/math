import Sude.ActiveRectangleCardinality
import Sude.LayerTranspose

/-! Exact occupancy of active complete rectangles and disjoint packed layer
supports. This concerns only supplied geometry, not FW activity or values. -/
namespace Sude
noncomputable section

/-- A packed sequence has exactly two cells per vertex per layer. -/
theorem packed_layers_support_card {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (LayerPacking.Layer n)} (h : LayerPacking.PackedLayers reserved layers) :
    (LayerPacking.layersSupport layers).card = 2 * n * layers.length := by
  classical
  have himage : (Finset.univ : Finset (Fin layers.length × (Fin n × Bool))).image
      (LayerPacking.sequenceCell layers) = LayerPacking.layersSupport layers := by
    ext z
    constructor
    · intro hz
      obtain ⟨⟨i, x⟩, _, rfl⟩ := Finset.mem_image.mp hz
      exact LayerPacking.layerSupport_subset _ layers (List.get_mem layers i)
        (LayerPacking.sequenceCell_mem layers i x)
    · intro hz
      obtain ⟨x, hx⟩ := LayerPacking.sequenceCell_covers layers z hz
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩
  rw [← himage, Finset.card_image_of_injective _ h.sequenceCell_injective]
  simp [Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm]

private theorem rowUsed_disjoint {n : ℕ} {A B : Finset (Cell n)}
    (h : Disjoint A B) (r : Fin n) :
    Disjoint (LayerPacking.rowUsed A r) (LayerPacking.rowUsed B r) := by
  apply Finset.disjoint_left.mpr
  intro c ha hb
  have ha' : (r, c) ∈ A := by simpa [LayerPacking.rowUsed] using ha
  have hb' : (r, c) ∈ B := by simpa [LayerPacking.rowUsed] using hb
  exact Finset.disjoint_left.mp h ha' hb'

private theorem colUsed_disjoint {n : ℕ} {A B : Finset (Cell n)}
    (h : Disjoint A B) (c : Fin n) :
    Disjoint (LayerPacking.colUsed A c) (LayerPacking.colUsed B c) := by
  apply Finset.disjoint_left.mpr
  intro r ha hb
  have ha' : (r, c) ∈ A := by simpa [LayerPacking.colUsed] using ha
  have hb' : (r, c) ∈ B := by simpa [LayerPacking.colUsed] using hb
  exact Finset.disjoint_left.mp h ha' hb'

/-- The actual support is exactly the active corners and the two layer
supports; these geometric reservations are assumed pairwise disjoint. -/
theorem active_rectangle_packed_layer_occupancy {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) (active : Finset (Fin L))
    (rows cols : List (LayerPacking.Layer n))
    (rowReserved colReserved : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers rowReserved rows)
    (hcols : LayerPacking.PackedLayers colReserved cols)
    (hrectRow : Disjoint (activeRectangleSupport hs choice active) (LayerPacking.layersSupport rows))
    (hrectCol : Disjoint (activeRectangleSupport hs choice active)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)))
    (hrowCol : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols))) :
    let rect := activeRectangleSupport hs choice active
    let rset := LayerPacking.layersSupport rows
    let cset := LayerPacking.transposeCells (LayerPacking.layersSupport cols)
    let total := rect ∪ rset ∪ cset
    total.card = 4 * active.card + 2 * n * (rows.length + cols.length) ∧
    (∀ r, (LayerPacking.rowUsed total r).card = (LayerPacking.rowUsed rect r).card +
      2 * (rows.length + cols.length)) ∧
    (∀ c, (LayerPacking.colUsed total c).card = (LayerPacking.colUsed rect c).card +
      2 * (rows.length + cols.length)) ∧
    (∀ r, (LayerPacking.rowUsed total r).card = 2 * (rows.length + cols.length) ∨
      (LayerPacking.rowUsed total r).card = 2 * (rows.length + cols.length) + 2) ∧
    (∀ c, (LayerPacking.colUsed total c).card = 2 * (rows.length + cols.length) ∨
      (LayerPacking.colUsed total c).card = 2 * (rows.length + cols.length) + 2) := by
  classical
  dsimp only
  have hrectRowCol : Disjoint (activeRectangleSupport hs choice active ∪ LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := Finset.disjoint_union_left.mpr ⟨hrectCol, hrowCol⟩
  have hcolCard : (LayerPacking.transposeCells (LayerPacking.layersSupport cols)).card =
      2 * n * cols.length := by
    unfold LayerPacking.transposeCells
    rw [Finset.card_image_of_injective _]
    · exact packed_layers_support_card hcols
    · intro a b hab
      have h := congrArg Prod.swap hab
      simpa using h
  have hrowR (r : Fin n) : (LayerPacking.rowUsed (LayerPacking.layersSupport rows) r).card = 2 * rows.length := by
    rw [LayerPacking.rowUsed_card_eq]
    exact hrows.row_balance r
  have hrowC (r : Fin n) : (LayerPacking.rowUsed (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) r).card = 2 * cols.length := by
    rw [LayerPacking.rowUsed_transpose, LayerPacking.colUsed_card_eq]
    exact hcols.column_balance r
  have hcolR (c : Fin n) : (LayerPacking.colUsed (LayerPacking.layersSupport rows) c).card = 2 * rows.length := by
    rw [LayerPacking.colUsed_card_eq]
    exact hrows.column_balance c
  have hcolC (c : Fin n) : (LayerPacking.colUsed (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) c).card = 2 * cols.length := by
    rw [LayerPacking.colUsed_transpose, LayerPacking.rowUsed_card_eq]
    exact hcols.row_balance c
  constructor
  · rw [Finset.card_union_of_disjoint hrectRowCol, Finset.card_union_of_disjoint hrectRow,
      active_rectangle_support_card, packed_layers_support_card hrows, hcolCard]
    ring
  have hrowExact (r : Fin n) :
      (LayerPacking.rowUsed (activeRectangleSupport hs choice active ∪
        LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) r).card =
      (LayerPacking.rowUsed (activeRectangleSupport hs choice active) r).card +
        2 * (rows.length + cols.length) := by
    rw [LayerPacking.rowUsed_union,
      Finset.card_union_of_disjoint (rowUsed_disjoint hrectRowCol r), LayerPacking.rowUsed_union,
      Finset.card_union_of_disjoint (rowUsed_disjoint hrectRow r), hrowR, hrowC]
    omega
  have hcolExact (c : Fin n) :
      (LayerPacking.colUsed (activeRectangleSupport hs choice active ∪
        LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) c).card =
      (LayerPacking.colUsed (activeRectangleSupport hs choice active) c).card +
        2 * (rows.length + cols.length) := by
    rw [LayerPacking.colUsed_union,
      Finset.card_union_of_disjoint (colUsed_disjoint hrectRowCol c), LayerPacking.colUsed_union,
      Finset.card_union_of_disjoint (colUsed_disjoint hrectRow c), hcolR, hcolC]
    omega
  refine ⟨hrowExact, hcolExact, ?_, ?_⟩
  · intro r
    rw [hrowExact]
    rcases active_rectangle_row_count hs choice active r with h | h <;> omega
  · intro c
    rw [hcolExact]
    rcases active_rectangle_column_count hs choice active c with h | h <;> omega

end
end Sude
