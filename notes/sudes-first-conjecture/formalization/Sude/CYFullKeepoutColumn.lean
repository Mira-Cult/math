import Sude.CYFullKeepoutGeometry
import Sude.FWFullReservationLineIncidence

namespace Sude
noncomputable section

theorem cy_rect_column_set {L n : ℕ} (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (i : Fin L) (c : Fin n)
    (hc : RectanglePacking.firstColumn hs choice i = c ∨ RectanglePacking.secondColumn hs choice i = c) :
    LayerPacking.colUsed (packedRectangleSupport hs choice) c =
      {RectanglePacking.firstRow hs i, RectanglePacking.secondRow hs i} := by
  classical
  apply Finset.Subset.antisymm
  · intro r hr
    have hcell : (r,c) ∈ packedRectangleSupport hs choice := by simpa [LayerPacking.colUsed] using hr
    obtain ⟨⟨j,t⟩, _, he⟩ := Finset.mem_image.mp hcell
    have hjj : (packedRectangleCorner hs choice (j,t)).2 =
        (packedRectangleCorner hs choice (i, if RectanglePacking.firstColumn hs choice i = c then 0 else 1)).2 := by
      rw [he]
      split_ifs <;> simp_all [packedRectangleCorner]
    have : j=i := packedCorner_column_label hs choice j i t _ hjj
    subst j
    have hh := packedCorner_row_cases hs choice i t
    rw [he] at hh
    simpa using hh
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hc with hc | hc <;> rcases hr with hr | hr <;> subst r <;>
      simp only [LayerPacking.colUsed, Finset.mem_filter, Finset.mem_univ, true_and]
    · rw [← hc]
      exact Finset.mem_image.mpr ⟨(i,0), Finset.mem_univ _, by simp [packedRectangleCorner]⟩
    · rw [← hc]
      exact Finset.mem_image.mpr ⟨(i,2), Finset.mem_univ _, by simp [packedRectangleCorner]⟩
    · rw [← hc]
      exact Finset.mem_image.mpr ⟨(i,1), Finset.mem_univ _, by simp [packedRectangleCorner]⟩
    · rw [← hc]
      exact Finset.mem_image.mpr ⟨(i,3), Finset.mem_univ _, by simp [packedRectangleCorner]⟩

theorem cy_second_column_ne_rev {L n : ℕ} (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (i : Fin L) :
    RectanglePacking.secondColumn hs choice i ≠ (RectanglePacking.secondColumn hs choice i).rev := by
  unfold RectanglePacking.secondColumn RectanglePacking.designated
  split_ifs <;> simp [RectanglePacking.low_ne_rev_low, Ne.symm (RectanglePacking.low_ne_rev_low hs _ _)]

theorem cy_second_column_is_q4 {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (i : Fin L) :
    (LayerPacking.colUsed (packedRectangleSupport hs choice ∪ (mainCells n ∪ antiCells n))
      (RectanglePacking.secondColumn hs choice i)).card = 4 := by
  classical
  let c := RectanglePacking.secondColumn hs choice i
  have hr := cy_rect_column_set hs choice i c (Or.inr rfl)
  have hd := cy_col_diagonal_used c
  have ho1 := RectanglePacking.firstRow_secondColumn_off_diagonals hs hL choice i
  have ho2 := RectanglePacking.secondRow_secondColumn_off_diagonals hs hL choice i
  have hdis : Disjoint (LayerPacking.colUsed (packedRectangleSupport hs choice) c)
      (LayerPacking.colUsed (mainCells n ∪ antiCells n) c) := by
    rw [hr]
    apply Finset.disjoint_left.mpr
    intro r hr hd
    have hd' : (r,c) ∈ mainCells n ∪ antiCells n := by simpa [LayerPacking.colUsed] using hd
    have hrows : r = RectanglePacking.firstRow hs i ∨ r = RectanglePacking.secondRow hs i := by simpa using hr
    rcases hrows with rfl | rfl <;> simp only [Finset.mem_union] at hd'
    · exact hd'.elim ho1.1 ho1.2
    · exact hd'.elim ho2.1 ho2.2
  rw [LayerPacking.colUsed_union, Finset.card_union_of_disjoint hdis, hr, hd]
  have hneq : c ≠ c.rev := cy_second_column_ne_rev hs choice i
  simp [RectanglePacking.firstRow_ne_secondRow hs i i, hneq]

end
end Sude
namespace Sude
noncomputable section

theorem cy_q4_column_is_second {L n : ℕ} (hs : 2*L+1 ≤ n) (_hL : 3 ≤ L)
    (choice : Fin L → Bool) (c : Fin n)
    (hq4 : (LayerPacking.colUsed (packedRectangleSupport hs choice ∪ (mainCells n ∪ antiCells n)) c).card = 4) :
    ∃ i : Fin L, RectanglePacking.secondColumn hs choice i = c := by
  classical
  have hrectcases := active_rectangle_column_count hs choice Finset.univ c
  have heq : activeRectangleSupport hs choice Finset.univ = packedRectangleSupport hs choice := by
    simp [activeRectangleSupport, packedRectangleSupport]
  rw [heq] at hrectcases
  have hd := cy_col_diagonal_used c
  have hdiagcard : (LayerPacking.colUsed (mainCells n ∪ antiCells n) c).card ≤ 2 := by rw [hd]; exact Finset.card_le_two
  have hsum := Finset.card_union_le (LayerPacking.colUsed (packedRectangleSupport hs choice) c)
    (LayerPacking.colUsed (mainCells n ∪ antiCells n) c)
  have hq : (LayerPacking.colUsed (packedRectangleSupport hs choice) c ∪
      LayerPacking.colUsed (mainCells n ∪ antiCells n) c).card = 4 := by simpa [LayerPacking.colUsed_union] using hq4
  have hrectcard : (LayerPacking.colUsed (packedRectangleSupport hs choice) c).card = 2 := by omega
  have hpos : 0 < (LayerPacking.colUsed (packedRectangleSupport hs choice) c).card := by omega
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos
  have hcell : (r,c) ∈ packedRectangleSupport hs choice := by simpa [LayerPacking.colUsed] using hr
  obtain ⟨⟨i,s⟩, _, he⟩ := Finset.mem_image.mp hcell
  have hcases := packedCorner_column_cases hs choice i s
  rw [he] at hcases
  rcases hcases with hfirst | hsecond
  · exfalso
    have hrset := cy_rect_column_set hs choice i c (Or.inl hfirst.symm)
    have hcorner : (RectanglePacking.firstRow hs i, c) ∈ mainCells n ∪ antiCells n := by
      have hg := RectanglePacking.designated_corner_geometry hs choice i
      cases hch : choice i
      · exact Finset.mem_union_right _ (by simpa [← hfirst] using (hg.2 hch).1)
      · exact Finset.mem_union_left _ (by simpa [← hfirst] using (hg.1 hch).1)
    have hmem : RectanglePacking.firstRow hs i ∈
        LayerPacking.colUsed (packedRectangleSupport hs choice) c ∩
          LayerPacking.colUsed (mainCells n ∪ antiCells n) c := by
      apply Finset.mem_inter.mpr
      constructor
      · rw [hrset]; simp
      · simpa [LayerPacking.colUsed] using hcorner
    have hinter : 0 < (LayerPacking.colUsed (packedRectangleSupport hs choice) c ∩
          LayerPacking.colUsed (mainCells n ∪ antiCells n) c).card := Finset.card_pos.mpr ⟨_, hmem⟩
    have hu := Finset.card_union_add_card_inter (LayerPacking.colUsed (packedRectangleSupport hs choice) c)
      (LayerPacking.colUsed (mainCells n ∪ antiCells n) c)
    omega
  · exact ⟨i, hsecond.symm⟩

theorem cy_column_q4_iff {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (c : Fin n) :
    (LayerPacking.colUsed (packedRectangleSupport hs choice ∪ (mainCells n ∪ antiCells n)) c).card = 4 ↔
      ∃ i : Fin L, RectanglePacking.secondColumn hs choice i = c := by
  constructor
  · exact cy_q4_column_is_second hs hL choice c
  · rintro ⟨i, rfl⟩
    exact cy_second_column_is_q4 hs hL choice i

theorem cy_column_q4_card {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) :
    ((Finset.univ : Finset (Fin n)).filter (fun c =>
      (LayerPacking.colUsed (packedRectangleSupport hs choice ∪ (mainCells n ∪ antiCells n)) c).card = 4)).card = L := by
  classical
  have heq : (Finset.univ : Finset (Fin n)).filter (fun c =>
      (LayerPacking.colUsed (packedRectangleSupport hs choice ∪ (mainCells n ∪ antiCells n)) c).card = 4) =
      Finset.univ.image (RectanglePacking.secondColumn hs choice) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rw [cy_column_q4_iff hs hL choice c]
  rw [heq, Finset.card_image_of_injective _ (RectanglePacking.secondColumn_injective hs choice)]
  simp
end
end Sude
namespace Sude
noncomputable section

theorem cy_first_column_ne_rev {L n : ℕ} (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (i : Fin L) :
    RectanglePacking.firstColumn hs choice i ≠ (RectanglePacking.firstColumn hs choice i).rev := by
  unfold RectanglePacking.firstColumn RectanglePacking.designated
  split_ifs <;> simp [RectanglePacking.low_ne_rev_low, Ne.symm (RectanglePacking.low_ne_rev_low hs _ _)]

theorem cy_first_column_is_q3 {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (i : Fin L) :
    (LayerPacking.colUsed (packedRectangleSupport hs choice ∪ (mainCells n ∪ antiCells n))
      (RectanglePacking.firstColumn hs choice i)).card = 3 := by
  classical
  let c := RectanglePacking.firstColumn hs choice i
  have hr := cy_rect_column_set hs choice i c (Or.inl rfl)
  have hd := cy_col_diagonal_used c
  have ho := RectanglePacking.secondRow_firstColumn_off_diagonals hs hL choice i
  have hc : (RectanglePacking.firstRow hs i, c) ∈ mainCells n ∪ antiCells n := by
    have hg := RectanglePacking.designated_corner_geometry hs choice i
    cases hch : choice i
    · exact Finset.mem_union_right _ (by simpa [c] using (hg.2 hch).1)
    · exact Finset.mem_union_left _ (by simpa [c] using (hg.1 hch).1)
  have hinter : LayerPacking.colUsed (packedRectangleSupport hs choice) c ∩
      LayerPacking.colUsed (mainCells n ∪ antiCells n) c = {RectanglePacking.firstRow hs i} := by
    apply Finset.Subset.antisymm
    · intro r h
      obtain ⟨hr', hd'⟩ := Finset.mem_inter.mp h
      rw [hr] at hr'
      have hrows : r = RectanglePacking.firstRow hs i ∨ r = RectanglePacking.secondRow hs i := by simpa using hr'
      rcases hrows with rfl | rfl
      · simp
      · have hd'' : (RectanglePacking.secondRow hs i,c) ∈ mainCells n ∪ antiCells n := by
          simpa [LayerPacking.colUsed] using hd'
        rcases Finset.mem_union.mp hd'' with hm | ha
        · exact (ho.1 hm).elim
        · exact (ho.2 ha).elim
    · intro r h
      have heq : r = RectanglePacking.firstRow hs i := by simpa using h
      subst r
      apply Finset.mem_inter.mpr
      constructor
      · rw [hr]; simp
      · simpa [LayerPacking.colUsed] using hc
  have hrcard : (LayerPacking.colUsed (packedRectangleSupport hs choice) c).card = 2 := by
    rw [hr]; simp [RectanglePacking.firstRow_ne_secondRow hs i i]
  have hdc : (LayerPacking.colUsed (mainCells n ∪ antiCells n) c).card = 2 := by
    rw [hd]; simp [c, cy_first_column_ne_rev hs choice i]
  have hu := Finset.card_union_add_card_inter (LayerPacking.colUsed (packedRectangleSupport hs choice) c)
    (LayerPacking.colUsed (mainCells n ∪ antiCells n) c)
  rw [hinter] at hu
  simp only [Finset.card_singleton] at hu
  change (LayerPacking.colUsed (packedRectangleSupport hs choice ∪ (mainCells n ∪ antiCells n)) c).card = 3
  rw [LayerPacking.colUsed_union]
  omega

theorem cy_center_of_rev_fixed {n : ℕ} (hn : 0 < n) (c : Fin n) (h : c = c.rev) :
    c = centerIndex n hn := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  change c.val = n - (c.val + 1) at hv
  change c.val = n / 2
  have hc := c.isLt
  omega

theorem cy_uncovered_noncenter_column_q2 {L n : ℕ} (hs : 2*L+1 ≤ n) (hn : 0 < n)
    (choice : Fin L → Bool) (c : Fin n) (hcenter : c ≠ centerIndex n hn)
    (hfirst : ∀ i : Fin L, RectanglePacking.firstColumn hs choice i ≠ c)
    (hsecond : ∀ i : Fin L, RectanglePacking.secondColumn hs choice i ≠ c) :
    (LayerPacking.colUsed (packedRectangleSupport hs choice ∪ (mainCells n ∪ antiCells n)) c).card = 2 := by
  classical
  have he : LayerPacking.colUsed (packedRectangleSupport hs choice) c = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hcell : (r,c) ∈ packedRectangleSupport hs choice := by simpa [LayerPacking.colUsed] using hr
    obtain ⟨⟨i,s⟩, _, he⟩ := Finset.mem_image.mp hcell
    have hcases := packedCorner_column_cases hs choice i s
    rw [he] at hcases
    exact hcases.elim (fun h => hfirst i h.symm) (fun h => hsecond i h.symm)
  have hne : c ≠ c.rev := fun h => hcenter (cy_center_of_rev_fixed hn c h)
  rw [LayerPacking.colUsed_union, he]
  simp [cy_col_diagonal_used, hne]
end
end Sude
