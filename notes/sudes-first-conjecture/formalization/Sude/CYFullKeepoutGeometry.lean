import Sude.CentralExactPool
import Sude.PackedRectangleLoads

namespace Sude
noncomputable section

theorem cy_rev_eq_center {n : ℕ} (hn : 0<n) (hodd : Odd n) (i : Fin n) :
    i.rev = i ↔ i = centerIndex n hn := by
  constructor
  · intro hi
    apply Fin.ext
    have hv := congrArg Fin.val hi
    change n - (i.val + 1) = i.val at hv
    change i.val = n / 2
    obtain ⟨k, hk⟩ := hodd
    have hi' := i.isLt
    omega
  · intro hi
    subst i
    exact centerIndex_rev n hn hodd

theorem cy_row_diagonal_used {n : ℕ} (r : Fin n) :
    LayerPacking.rowUsed (mainCells n ∪ antiCells n) r = {r, r.rev} := by
  ext c
  simp [LayerPacking.rowUsed, mem_mainCells, mem_antiCells, eq_comm]

theorem cy_col_diagonal_used {n : ℕ} (c : Fin n) :
    LayerPacking.colUsed (mainCells n ∪ antiCells n) c = {c, c.rev} := by
  ext r
  have he : c = r.rev ↔ r = c.rev := by
    constructor <;> intro h <;> have hh := congrArg Fin.rev h <;> simpa using hh.symm
  simp [LayerPacking.colUsed, mem_mainCells, mem_antiCells, eq_comm, he]

theorem cy_diagonal_line_card {n : ℕ} (hn : 0<n) (hodd : Odd n) (i : Fin n) :
    (LayerPacking.rowUsed (mainCells n ∪ antiCells n) i).card =
      if i = centerIndex n hn then 1 else 2 := by
  rw [cy_row_diagonal_used]
  by_cases h : i = centerIndex n hn
  · subst i
    simp [centerIndex_rev n hn hodd]
  · have hrev : i.rev ≠ i := fun he => h ((cy_rev_eq_center hn hodd i).1 he)
    simp [h, Ne.symm hrev]

theorem cy_diagonal_col_card {n : ℕ} (hn : 0<n) (hodd : Odd n) (i : Fin n) :
    (LayerPacking.colUsed (mainCells n ∪ antiCells n) i).card =
      if i = centerIndex n hn then 1 else 2 := by
  rw [cy_col_diagonal_used, ← cy_row_diagonal_used]
  exact cy_diagonal_line_card hn hodd i


theorem cy_rect_center_row_empty {L n : ℕ} (hs : 2*L+1 ≤ n) (hn : 0<n)
    (choice : Fin L → Bool) :
    LayerPacking.rowUsed (packedRectangleSupport hs choice) (centerIndex n hn) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  have hcell : (centerIndex n hn,c) ∈ packedRectangleSupport hs choice := by simpa [LayerPacking.rowUsed] using hc
  obtain ⟨⟨i,s⟩, _, heq⟩ := Finset.mem_image.mp hcell
  have hr := packedCorner_row_cases hs choice i s
  rw [heq] at hr
  rcases hr with hr | hr
  · exact (RectanglePacking.low_ne_center hs hn i) hr.symm
  · exact (RectanglePacking.rev_low_ne_center hs hn (RectanglePacking.next L i)) hr.symm

theorem cy_first_col_ne_center {L n : ℕ} (hs : 2*L+1 ≤ n) (hn : 0<n)
    (choice : Fin L → Bool) (i : Fin L) : RectanglePacking.firstColumn hs choice i ≠ centerIndex n hn := by
  cases hi : choice i
  · simpa [RectanglePacking.firstColumn, RectanglePacking.designated, hi] using RectanglePacking.rev_low_ne_center hs hn i
  · simpa [RectanglePacking.firstColumn, RectanglePacking.designated, hi] using RectanglePacking.low_ne_center hs hn i

theorem cy_second_col_ne_center {L n : ℕ} (hs : 2*L+1 ≤ n) (hn : 0<n)
    (choice : Fin L → Bool) (i : Fin L) : RectanglePacking.secondColumn hs choice i ≠ centerIndex n hn := by
  cases hi : choice (RectanglePacking.nextTwo L i)
  · simpa [RectanglePacking.secondColumn, RectanglePacking.designated, hi] using RectanglePacking.low_ne_center hs hn (RectanglePacking.nextTwo L i)
  · simpa [RectanglePacking.secondColumn, RectanglePacking.designated, hi] using RectanglePacking.rev_low_ne_center hs hn (RectanglePacking.nextTwo L i)

theorem cy_rect_center_col_empty {L n : ℕ} (hs : 2*L+1 ≤ n) (hn : 0<n)
    (choice : Fin L → Bool) :
    LayerPacking.colUsed (packedRectangleSupport hs choice) (centerIndex n hn) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hcell : (r,centerIndex n hn) ∈ packedRectangleSupport hs choice := by simpa [LayerPacking.colUsed] using hr
  obtain ⟨⟨i,s⟩, _, heq⟩ := Finset.mem_image.mp hcell
  have hc := packedCorner_column_cases hs choice i s
  rw [heq] at hc
  rcases hc with hc | hc
  · exact cy_first_col_ne_center hs hn choice i hc.symm
  · exact cy_second_col_ne_center hs hn choice i hc.symm

theorem cy_rect_diag_center_lines {L n : ℕ} (hs : 2*L+1 ≤ n) (hn : 0<n) (hodd : Odd n)
    (choice : Fin L → Bool) :
    (LayerPacking.rowUsed (packedRectangleSupport hs choice ∪ (mainCells n ∪ antiCells n)) (centerIndex n hn)).card = 1 ∧
    (LayerPacking.colUsed (packedRectangleSupport hs choice ∪ (mainCells n ∪ antiCells n)) (centerIndex n hn)).card = 1 := by
  rw [LayerPacking.rowUsed_union, LayerPacking.colUsed_union,
    cy_rect_center_row_empty hs hn choice, cy_rect_center_col_empty hs hn choice]
  simp only [Finset.empty_union]
  exact ⟨by simpa using cy_diagonal_line_card hn hodd (centerIndex n hn),
    by simpa using cy_diagonal_col_card hn hodd (centerIndex n hn)⟩

end
end Sude

namespace Sude
noncomputable section

theorem cy_diag_corner_side {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (i : Fin L) (s : Fin 4)
    (hd : packedRectangleCorner hs choice (i,s) ∈ mainCells n ∪ antiCells n) : s = 0 := by
  have h01 := RectanglePacking.firstRow_secondColumn_off_diagonals hs hL choice i
  have h10 := RectanglePacking.secondRow_firstColumn_off_diagonals hs hL choice i
  have h11 := RectanglePacking.secondRow_secondColumn_off_diagonals hs hL choice i
  fin_cases s <;> simp_all [packedRectangleCorner, Finset.mem_union]

theorem cy_diag_corner_mem {L n : ℕ} (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (i : Fin L) :
    packedRectangleCorner hs choice (i,0) ∈ mainCells n ∪ antiCells n := by
  have hg := RectanglePacking.designated_corner_geometry hs choice i
  cases hi : choice i
  · exact Finset.mem_union_right _ (by simpa [packedRectangleCorner] using (hg.2 hi).1)
  · exact Finset.mem_union_left _ (by simpa [packedRectangleCorner] using (hg.1 hi).1)


end
end Sude
