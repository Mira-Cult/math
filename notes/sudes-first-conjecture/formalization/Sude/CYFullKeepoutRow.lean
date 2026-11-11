import Sude.CYFullKeepoutGeometry
import Sude.ActiveRectangleLineCounts

namespace Sude
noncomputable section

theorem cy_row_intersection_iff {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (r : Fin n) :
    Disjoint (LayerPacking.rowUsed (packedRectangleSupport hs choice) r)
      (LayerPacking.rowUsed (mainCells n ∪ antiCells n) r) ↔
      ¬ ∃ i : Fin L, RectanglePacking.firstRow hs i = r := by
  classical
  constructor
  · intro hd ⟨i, hi⟩
    let c := RectanglePacking.firstColumn hs choice i
    have hrect : c ∈ LayerPacking.rowUsed (packedRectangleSupport hs choice) r := by
      simp only [LayerPacking.rowUsed, Finset.mem_filter, Finset.mem_univ, true_and]
      apply Finset.mem_image.mpr
      refine ⟨(i,0), Finset.mem_univ _, ?_⟩
      simp [packedRectangleCorner, hi, c]
    have hdiag : c ∈ LayerPacking.rowUsed (mainCells n ∪ antiCells n) r := by
      simp only [LayerPacking.rowUsed, Finset.mem_filter, Finset.mem_univ, true_and]
      have h := cy_diag_corner_mem hs choice i
      simpa [packedRectangleCorner, hi, c] using h
    exact Finset.disjoint_left.mp hd hrect hdiag
  · intro hnone
    apply Finset.disjoint_left.mpr
    intro c hrect hdiag
    have hcell : (r,c) ∈ packedRectangleSupport hs choice := by simpa [LayerPacking.rowUsed] using hrect
    have hcellD : (r,c) ∈ mainCells n ∪ antiCells n := by simpa [LayerPacking.rowUsed] using hdiag
    obtain ⟨⟨i,s⟩, _, heq⟩ := Finset.mem_image.mp hcell
    have hzero : s = 0 := cy_diag_corner_side hs hL choice i s (heq ▸ hcellD)
    subst s
    apply hnone
    refine ⟨i, ?_⟩
    have hh := congrArg Prod.fst heq
    simpa [packedRectangleCorner] using hh

theorem cy_second_row_disjoint {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (i : Fin L) :
    Disjoint (LayerPacking.rowUsed (packedRectangleSupport hs choice) (RectanglePacking.secondRow hs i))
      (LayerPacking.rowUsed (mainCells n ∪ antiCells n) (RectanglePacking.secondRow hs i)) := by
  apply (cy_row_intersection_iff hs hL choice _).2
  rintro ⟨j,hj⟩
  exact RectanglePacking.firstRow_ne_secondRow hs j i hj
end
end Sude
namespace Sude
noncomputable section

/-- A full rectangle row has load two iff it is one of the disjoint first/second row slots. -/
theorem cy_full_rect_row_two_iff {L n : ℕ} (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (r : Fin n) :
    (LayerPacking.rowUsed (packedRectangleSupport hs choice) r).card = 2 ↔
      (∃ i, RectanglePacking.firstRow hs i = r) ∨ (∃ i, RectanglePacking.secondRow hs i = r) := by
  classical
  have hcard := active_rectangle_row_count hs choice Finset.univ r
  have heq : activeRectangleSupport hs choice Finset.univ = packedRectangleSupport hs choice := by
    simp [activeRectangleSupport, packedRectangleSupport]
  rw [heq] at hcard
  constructor
  · intro htwo
    have hpos : 0 < (LayerPacking.rowUsed (packedRectangleSupport hs choice) r).card := by omega
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
    have hcell : (r,c) ∈ packedRectangleSupport hs choice := by simpa [LayerPacking.rowUsed] using hc
    obtain ⟨⟨i,s⟩, _, heq⟩ := Finset.mem_image.mp hcell
    have hr : (packedRectangleCorner hs choice (i,s)).1 = r := congrArg Prod.fst heq
    rcases packedCorner_row_cases hs choice i s with hf | hs'
    · exact Or.inl ⟨i, hf.symm.trans hr⟩
    · exact Or.inr ⟨i, hs'.symm.trans hr⟩
  · intro h
    have hne : (LayerPacking.rowUsed (packedRectangleSupport hs choice) r).Nonempty := by
      rcases h with ⟨i, hr⟩ | ⟨i, hr⟩
      · refine ⟨RectanglePacking.firstColumn hs choice i, ?_⟩
        have hm : packedRectangleCorner hs choice (i,0) ∈ packedRectangleSupport hs choice :=
          Finset.mem_image.mpr ⟨(i,0), Finset.mem_univ _, rfl⟩
        simpa [LayerPacking.rowUsed, packedRectangleCorner, hr] using hm
      · refine ⟨RectanglePacking.firstColumn hs choice i, ?_⟩
        have hm : packedRectangleCorner hs choice (i,2) ∈ packedRectangleSupport hs choice :=
          Finset.mem_image.mpr ⟨(i,2), Finset.mem_univ _, rfl⟩
        simpa [LayerPacking.rowUsed, packedRectangleCorner, hr] using hm
    have hpos := Finset.card_pos.mpr hne
    rcases hcard with hc | hc <;> omega
end
end Sude
namespace Sude
noncomputable section

theorem cy_row_diagonal_card {n : ℕ} (hn : 0<n) (hodd : Odd n) (r : Fin n)
    (hcenter : r ≠ centerIndex n hn) :
    (LayerPacking.rowUsed (mainCells n ∪ antiCells n) r).card = 2 := by
  simpa [hcenter] using cy_diagonal_line_card hn hodd r
end
end Sude
namespace Sude
noncomputable section

/-- Exactly the second-row image has four occupied rectangle-or-diagonal cells. -/
theorem cy_row_q4_iff {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (hn : 0 < n) (hodd : Odd n) (choice : Fin L → Bool) (r : Fin n) :
    (LayerPacking.rowUsed (packedRectangleSupport hs choice ∪ (mainCells n ∪ antiCells n)) r).card = 4 ↔
      ∃ i : Fin L, RectanglePacking.secondRow hs i = r := by
  classical
  constructor
  · intro hfour
    rw [LayerPacking.rowUsed_union] at hfour
    have hrect : (LayerPacking.rowUsed (packedRectangleSupport hs choice) r).card ≤ 2 :=
      packedRectangleSupport_row_load hs choice r
    have hdiag : (LayerPacking.rowUsed (mainCells n ∪ antiCells n) r).card ≤ 2 := by
      rw [cy_row_diagonal_used]
      exact Finset.card_le_two
    have hsum := Finset.card_union_add_card_inter
      (LayerPacking.rowUsed (packedRectangleSupport hs choice) r)
      (LayerPacking.rowUsed (mainCells n ∪ antiCells n) r)
    have hzero : (LayerPacking.rowUsed (packedRectangleSupport hs choice) r ∩
      LayerPacking.rowUsed (mainCells n ∪ antiCells n) r).card = 0 := by omega
    have hdis : Disjoint (LayerPacking.rowUsed (packedRectangleSupport hs choice) r)
        (LayerPacking.rowUsed (mainCells n ∪ antiCells n) r) := by
      exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hzero)
    have hnot := (cy_row_intersection_iff hs hL choice r).1 hdis
    have htwo : (LayerPacking.rowUsed (packedRectangleSupport hs choice) r).card = 2 := by omega
    rcases (cy_full_rect_row_two_iff hs choice r).1 htwo with hfirst | hsecond
    · exact False.elim (hnot hfirst)
    · exact hsecond
  · rintro ⟨i, rfl⟩
    have hcenter : RectanglePacking.secondRow hs i ≠ centerIndex n hn := by
      simpa [RectanglePacking.secondRow] using RectanglePacking.rev_low_ne_center hs hn (RectanglePacking.next L i)
    have hdiag := cy_row_diagonal_card hn hodd (RectanglePacking.secondRow hs i) hcenter
    have hrect := (cy_full_rect_row_two_iff hs choice _).2 (Or.inr ⟨i, rfl⟩)
    have hdis := cy_second_row_disjoint hs hL choice i
    rw [LayerPacking.rowUsed_union, Finset.card_union_of_disjoint hdis, hrect, hdiag]

/-- Exactly L rows hit q=4, including all spare-capacity labels. -/
theorem cy_row_q4_card {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (hn : 0 < n) (hodd : Odd n) (choice : Fin L → Bool) :
    ((Finset.univ : Finset (Fin n)).filter (fun r =>
      (LayerPacking.rowUsed (packedRectangleSupport hs choice ∪ (mainCells n ∪ antiCells n)) r).card = 4)).card = L := by
  classical
  have heq : ((Finset.univ : Finset (Fin n)).filter (fun r =>
      (LayerPacking.rowUsed (packedRectangleSupport hs choice ∪ (mainCells n ∪ antiCells n)) r).card = 4)) =
      Finset.univ.image (RectanglePacking.secondRow hs) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rw [cy_row_q4_iff hs hL hn hodd choice r]
  rw [heq, Finset.card_image_of_injective _ (RectanglePacking.secondRow_injective hs)]
  simp
end
end Sude
namespace Sude
noncomputable section

theorem cy_first_row_overlap_singleton {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (i : Fin L) :
    LayerPacking.rowUsed (packedRectangleSupport hs choice) (RectanglePacking.firstRow hs i) ∩
      LayerPacking.rowUsed (mainCells n ∪ antiCells n) (RectanglePacking.firstRow hs i) =
        {RectanglePacking.firstColumn hs choice i} := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨hr, hd⟩ := Finset.mem_inter.mp hc
    have hcell : (RectanglePacking.firstRow hs i,c) ∈ packedRectangleSupport hs choice := by
      simpa [LayerPacking.rowUsed] using hr
    have hdiag : (RectanglePacking.firstRow hs i,c) ∈ mainCells n ∪ antiCells n := by
      simpa [LayerPacking.rowUsed] using hd
    obtain ⟨⟨j,s⟩, _, heq⟩ := Finset.mem_image.mp hcell
    have hside := cy_diag_corner_side hs hL choice j s (heq ▸ hdiag)
    subst s
    have hrow : RectanglePacking.firstRow hs j = RectanglePacking.firstRow hs i := by
      have he := congrArg Prod.fst heq
      simpa [packedRectangleCorner] using he
    have hij := RectanglePacking.firstRow_injective hs hrow
    subst j
    have hcol := congrArg Prod.snd heq
    simpa [packedRectangleCorner] using hcol.symm
  · intro hc
    have he : c = RectanglePacking.firstColumn hs choice i := Finset.mem_singleton.mp hc
    subst c
    apply Finset.mem_inter.mpr
    constructor
    · have h : packedRectangleCorner hs choice (i,0) ∈ packedRectangleSupport hs choice :=
        Finset.mem_image.mpr ⟨(i,0), Finset.mem_univ _, rfl⟩
      simpa [LayerPacking.rowUsed, packedRectangleCorner] using h
    · have h := cy_diag_corner_mem hs choice i
      simpa [LayerPacking.rowUsed, packedRectangleCorner] using h

/-- First row of each rectangle has q=3 after both diagonals. -/
theorem cy_first_row_q3 {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (hn : 0 < n) (hodd : Odd n) (choice : Fin L → Bool) (i : Fin L) :
    (LayerPacking.rowUsed (packedRectangleSupport hs choice ∪ (mainCells n ∪ antiCells n))
      (RectanglePacking.firstRow hs i)).card = 3 := by
  classical
  have hcenter : RectanglePacking.firstRow hs i ≠ centerIndex n hn := by
    simpa [RectanglePacking.firstRow] using RectanglePacking.low_ne_center hs hn i
  have hdiag := cy_row_diagonal_card hn hodd (RectanglePacking.firstRow hs i) hcenter
  have hrect := (cy_full_rect_row_two_iff hs choice _).2 (Or.inl ⟨i, rfl⟩)
  have hinter := cy_first_row_overlap_singleton hs hL choice i
  have hsum := Finset.card_union_add_card_inter
    (LayerPacking.rowUsed (packedRectangleSupport hs choice) (RectanglePacking.firstRow hs i))
    (LayerPacking.rowUsed (mainCells n ∪ antiCells n) (RectanglePacking.firstRow hs i))
  rw [hinter] at hsum
  simp only [Finset.card_singleton] at hsum
  rw [LayerPacking.rowUsed_union]
  omega

/-- Noncentral rows outside both rectangle slot images have q=2. -/
theorem cy_plain_row_q2 {L n : ℕ} (hs : 2*L+1 ≤ n)
    (hn : 0 < n) (hodd : Odd n) (choice : Fin L → Bool) (r : Fin n)
    (hcenter : r ≠ centerIndex n hn)
    (hfirst : ¬ ∃ i, RectanglePacking.firstRow hs i = r)
    (hsecond : ¬ ∃ i, RectanglePacking.secondRow hs i = r) :
    (LayerPacking.rowUsed (packedRectangleSupport hs choice ∪ (mainCells n ∪ antiCells n)) r).card = 2 := by
  classical
  have hdiag := cy_row_diagonal_card hn hodd r hcenter
  have hcard := active_rectangle_row_count hs choice Finset.univ r
  have heq : activeRectangleSupport hs choice Finset.univ = packedRectangleSupport hs choice := by
    simp [activeRectangleSupport, packedRectangleSupport]
  rw [heq] at hcard
  have hnot : (LayerPacking.rowUsed (packedRectangleSupport hs choice) r).card ≠ 2 := by
    intro htwo
    rcases (cy_full_rect_row_two_iff hs choice r).1 htwo with hf | hs'
    · exact hfirst hf
    · exact hsecond hs'
  have hzero : (LayerPacking.rowUsed (packedRectangleSupport hs choice) r).card = 0 := by omega
  have hempty := Finset.card_eq_zero.mp hzero
  rw [LayerPacking.rowUsed_union, hempty, Finset.empty_union]
  exact hdiag
end
end Sude
