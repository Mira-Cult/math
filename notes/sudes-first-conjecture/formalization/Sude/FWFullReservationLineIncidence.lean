import Sude.FWJointPackedOccupancy

/-! Exact row and column incidence of the full geometric reservation.
No entry values or line-sum estimates are asserted. -/
namespace Sude
noncomputable section

/-- Each row and column contains `12*S` or `12*S+2` reserved cells under
the supplied FW layer lengths and normalized joint packings. -/
theorem fw_full_reservation_line_incidence {n P : ℕ}
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (hbc : bc.length = 5 * 3) (hsc : sc.length = 16 * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice)
      (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc)) :
    let S := 5 + 16 + 3 * (n / 450) + P
    let rows := (((br ++ sr) ++ wr) ++ gr)
    let cols := (((bc ++ sc) ++ wc) ++ gc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)
    (∀ r, (LayerPacking.rowUsed full r).card = 12 * S ∨
      (LayerPacking.rowUsed full r).card = 12 * S + 2) ∧
    (∀ c, (LayerPacking.colUsed full c).card = 12 * S ∨
      (LayerPacking.colUsed full c).card = 12 * S + 2) ∧
    (∀ r, ∃ q : ℕ, (q = 0 ∨ q = 2) ∧
      (LayerPacking.rowUsed full r).card = 12 * S + q ∧ 12 * S + q ≤ n) ∧
    (∀ c, ∃ q : ℕ, (q = 0 ∨ q = 2) ∧
      (LayerPacking.colUsed full c).card = 12 * S + q ∧ 12 * S + q ≤ n) := by
  classical
  dsimp only
  let rows := (((br ++ sr) ++ wr) ++ gr)
  let cols := (((bc ++ sc) ++ wc) ++ gc)
  have hall : activeRectangleSupport hs choice Finset.univ = packedRectangleSupport hs choice := by
    simp [activeRectangleSupport, packedRectangleSupport]
  have hrectRow : Disjoint (activeRectangleSupport hs choice Finset.univ)
      (LayerPacking.layersSupport rows) := by
    rw [hall]
    exact hrows.reserved_disjoint
  have hrectCol : Disjoint (activeRectangleSupport hs choice Finset.univ)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
    rw [hall]
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact (hcols.transposed_support_safe z hz').1 (Finset.mem_union_left _ hz)
  have hrowCol : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact (hcols.transposed_support_safe z hz').1 (Finset.mem_union_right _ hz)
  have h := active_rectangle_packed_layer_occupancy hs choice Finset.univ rows cols
    (packedRectangleSupport hs choice)
    (LayerPacking.transposeCells (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows))
    hrows hcols hrectRow hrectCol hrowCol
  dsimp only at h
  rw [hall] at h
  have hrl : rows.length = 3 * (5 + 16 + 3 * (n / 450) + P) := by
    simp only [rows, List.length_append, hbr, hsr, hwr, hgr]
    omega
  have hcl : cols.length = 3 * (5 + 16 + 3 * (n / 450) + P) := by
    simp only [cols, List.length_append, hbc, hsc, hwc, hgc]
    omega
  rw [hrl, hcl] at h
  have heq : 2 * (3 * (5 + 16 + 3 * (n / 450) + P) +
      3 * (5 + 16 + 3 * (n / 450) + P)) = 12 * (5 + 16 + 3 * (n / 450) + P) := by omega
  rw [heq] at h
  have hrow := h.2.2.2.1
  have hcol := h.2.2.2.2
  refine ⟨hrow, hcol, ?_, ?_⟩
  · intro r
    have hle : (LayerPacking.rowUsed (packedRectangleSupport hs choice ∪
        LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) r).card ≤ n := by
      have hh := Finset.card_le_card (Finset.subset_univ
        (LayerPacking.rowUsed (packedRectangleSupport hs choice ∪
          LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) r))
      simpa using hh
    rcases hrow r with hr | hr
    · exact ⟨0, Or.inl rfl, by omega, by omega⟩
    · exact ⟨2, Or.inr rfl, by omega, by omega⟩
  · intro c
    have hle : (LayerPacking.colUsed (packedRectangleSupport hs choice ∪
        LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) c).card ≤ n := by
      have hh := Finset.card_le_card (Finset.subset_univ
        (LayerPacking.colUsed (packedRectangleSupport hs choice ∪
          LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) c))
      simpa using hh
    rcases hcol c with hc | hc
    · exact ⟨0, Or.inl rfl, by omega, by omega⟩
    · exact ⟨2, Or.inr rfl, by omega, by omega⟩

end
end Sude
