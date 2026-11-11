import Sude.PackedRectangleLoads

/-! Exact line counts for an explicitly selected set of complete packed
rectangles. No claim is made about arbitrary subsets of their corners. -/
namespace Sude
noncomputable section

/-- All four corners, and only those corners, for selected rectangle labels. -/
def activeRectangleSupport {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (active : Finset (Fin L)) : Finset (Cell n) :=
  (active ×ˢ (Finset.univ : Finset (Fin 4))).image (packedRectangleCorner hs choice)

/-- A row meets the selected full rectangles in either zero or two cells. -/
theorem active_rectangle_row_count {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (active : Finset (Fin L)) (r : Fin n) :
    (LayerPacking.rowUsed (activeRectangleSupport hs choice active) r).card = 0 ∨
      (LayerPacking.rowUsed (activeRectangleSupport hs choice active) r).card = 2 := by
  classical
  by_cases hex : ∃ i ∈ active, ∃ side : Fin 4,
      (packedRectangleCorner hs choice (i, side)).1 = r
  · obtain ⟨i, hi, s, hrs⟩ := hex
    have hrow : RectanglePacking.firstRow hs i = r ∨ RectanglePacking.secondRow hs i = r := by
      have h := packedCorner_row_cases hs choice i s
      rcases h with h | h <;> [exact Or.inl (h.symm.trans hrs); exact Or.inr (h.symm.trans hrs)]
    have hset : LayerPacking.rowUsed (activeRectangleSupport hs choice active) r =
        {RectanglePacking.firstColumn hs choice i, RectanglePacking.secondColumn hs choice i} := by
      apply Finset.Subset.antisymm
      · intro c hc
        have hcell : (r, c) ∈ activeRectangleSupport hs choice active := by simpa [LayerPacking.rowUsed] using hc
        obtain ⟨⟨j, t⟩, hj, heq⟩ := Finset.mem_image.mp hcell
        have hjj : (packedRectangleCorner hs choice (j, t)).1 =
            (packedRectangleCorner hs choice (i, s)).1 := by rw [heq, hrs]
        have : j = i := packedCorner_row_label hs choice j i t s hjj
        subst j
        have hc' := packedCorner_column_cases hs choice i t
        rw [heq] at hc'
        simpa using hc'
      · intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hrow with hr | hr <;> rcases hc with hc | hc <;> subst c <;>
          simp only [LayerPacking.rowUsed, Finset.mem_filter, Finset.mem_univ, true_and]
        · rw [← hr]
          exact Finset.mem_image.mpr ⟨(i, 0), by simp [hi], by simp [packedRectangleCorner]⟩
        · rw [← hr]
          exact Finset.mem_image.mpr ⟨(i, 1), by simp [hi], by simp [packedRectangleCorner]⟩
        · rw [← hr]
          exact Finset.mem_image.mpr ⟨(i, 2), by simp [hi], by simp [packedRectangleCorner]⟩
        · rw [← hr]
          exact Finset.mem_image.mpr ⟨(i, 3), by simp [hi], by simp [packedRectangleCorner]⟩
    right
    rw [hset]
    simp [RectanglePacking.firstColumn_ne_secondColumn hs choice i i]
  · left
    have hempty : LayerPacking.rowUsed (activeRectangleSupport hs choice active) r = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c hc
      have hcell : (r, c) ∈ activeRectangleSupport hs choice active := by simpa [LayerPacking.rowUsed] using hc
      obtain ⟨⟨j, t⟩, hj, heq⟩ := Finset.mem_image.mp hcell
      have hj' : j ∈ active := (Finset.mem_product.mp hj).1
      exact hex ⟨j, hj', t, congrArg Prod.fst heq⟩
    simp [hempty]

/-- A column meets the selected full rectangles in either zero or two cells. -/
theorem active_rectangle_column_count {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (active : Finset (Fin L)) (c : Fin n) :
    (LayerPacking.colUsed (activeRectangleSupport hs choice active) c).card = 0 ∨
      (LayerPacking.colUsed (activeRectangleSupport hs choice active) c).card = 2 := by
  classical
  by_cases hex : ∃ i ∈ active, ∃ side : Fin 4,
      (packedRectangleCorner hs choice (i, side)).2 = c
  · obtain ⟨i, hi, s, hcs⟩ := hex
    have hcol : RectanglePacking.firstColumn hs choice i = c ∨ RectanglePacking.secondColumn hs choice i = c := by
      have h := packedCorner_column_cases hs choice i s
      rcases h with h | h <;> [exact Or.inl (h.symm.trans hcs); exact Or.inr (h.symm.trans hcs)]
    have hset : LayerPacking.colUsed (activeRectangleSupport hs choice active) c =
        {RectanglePacking.firstRow hs i, RectanglePacking.secondRow hs i} := by
      apply Finset.Subset.antisymm
      · intro r hr
        have hcell : (r, c) ∈ activeRectangleSupport hs choice active := by simpa [LayerPacking.colUsed] using hr
        obtain ⟨⟨j, t⟩, hj, heq⟩ := Finset.mem_image.mp hcell
        have hjj : (packedRectangleCorner hs choice (j, t)).2 =
            (packedRectangleCorner hs choice (i, s)).2 := by rw [heq, hcs]
        have : j = i := packedCorner_column_label hs choice j i t s hjj
        subst j
        have hr' := packedCorner_row_cases hs choice i t
        rw [heq] at hr'
        simpa using hr'
      · intro r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hcol with hc | hc <;> rcases hr with hr | hr <;> subst r <;>
          simp only [LayerPacking.colUsed, Finset.mem_filter, Finset.mem_univ, true_and]
        · rw [← hc]
          exact Finset.mem_image.mpr ⟨(i, 0), by simp [hi], by simp [packedRectangleCorner]⟩
        · rw [← hc]
          exact Finset.mem_image.mpr ⟨(i, 2), by simp [hi], by simp [packedRectangleCorner]⟩
        · rw [← hc]
          exact Finset.mem_image.mpr ⟨(i, 1), by simp [hi], by simp [packedRectangleCorner]⟩
        · rw [← hc]
          exact Finset.mem_image.mpr ⟨(i, 3), by simp [hi], by simp [packedRectangleCorner]⟩
    right
    rw [hset]
    simp [RectanglePacking.firstRow_ne_secondRow hs i i]
  · left
    have hempty : LayerPacking.colUsed (activeRectangleSupport hs choice active) c = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      have hcell : (r, c) ∈ activeRectangleSupport hs choice active := by simpa [LayerPacking.colUsed] using hr
      obtain ⟨⟨j, t⟩, hj, heq⟩ := Finset.mem_image.mp hcell
      have hj' : j ∈ active := (Finset.mem_product.mp hj).1
      exact hex ⟨j, hj', t, congrArg Prod.snd heq⟩
    simp [hempty]

/-- A direct upper-bound interface for the row count. -/
theorem active_rectangle_row_load_le_two {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (active : Finset (Fin L)) (r : Fin n) :
    (LayerPacking.rowUsed (activeRectangleSupport hs choice active) r).card ≤ 2 := by
  rcases active_rectangle_row_count hs choice active r with h | h <;> omega

/-- A direct upper-bound interface for the column count. -/
theorem active_rectangle_column_load_le_two {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (active : Finset (Fin L)) (c : Fin n) :
    (LayerPacking.colUsed (activeRectangleSupport hs choice active) c).card ≤ 2 := by
  rcases active_rectangle_column_count hs choice active c with h | h <;> omega

end
end Sude
