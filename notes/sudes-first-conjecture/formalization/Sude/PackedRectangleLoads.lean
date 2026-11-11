import Sude.BridgeRectangles
import Sude.LayerNetworks

/-! Exact line-load bounds for RP1 rectangles before ordinary layers. -/
namespace Sude
noncomputable section

/-- The actual cells of all rectangles in the joint RP1 packing. -/
def packedRectangleSupport {L n : ℕ} (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) : Finset (Cell n) :=
  (Finset.univ : Finset (Fin L × Fin 4)).image (packedRectangleCorner hs choice)

theorem packedCorner_row_label {L n : ℕ} (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (i j : Fin L) (s t : Fin 4)
    (h : (packedRectangleCorner hs choice (i, s)).1 = (packedRectangleCorner hs choice (j, t)).1) :
    i = j := by
  have h11 := RectanglePacking.firstRow_injective hs
  have h22 := RectanglePacking.secondRow_injective hs
  have h12 := RectanglePacking.firstRow_ne_secondRow hs
  fin_cases s <;> fin_cases t <;> simp [packedRectangleCorner] at h <;>
    first | exact h11 h | exact h22 h | exact False.elim (h12 _ _ h) |
      exact False.elim (h12 _ _ h.symm)

theorem packedCorner_column_label {L n : ℕ} (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (i j : Fin L) (s t : Fin 4)
    (h : (packedRectangleCorner hs choice (i, s)).2 = (packedRectangleCorner hs choice (j, t)).2) :
    i = j := by
  have h11 := RectanglePacking.firstColumn_injective hs choice
  have h22 := RectanglePacking.secondColumn_injective hs choice
  have h12 := RectanglePacking.firstColumn_ne_secondColumn hs choice
  fin_cases s <;> fin_cases t <;> simp [packedRectangleCorner] at h <;>
    first | exact h11 h | exact h22 h | exact False.elim (h12 _ _ h) |
      exact False.elim (h12 _ _ h.symm)

theorem packedCorner_column_cases {L n : ℕ} (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (i : Fin L) (s : Fin 4) :
    (packedRectangleCorner hs choice (i, s)).2 = RectanglePacking.firstColumn hs choice i ∨
      (packedRectangleCorner hs choice (i, s)).2 = RectanglePacking.secondColumn hs choice i := by
  fin_cases s <;> simp [packedRectangleCorner]

theorem packedCorner_row_cases {L n : ℕ} (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (i : Fin L) (s : Fin 4) :
    (packedRectangleCorner hs choice (i, s)).1 = RectanglePacking.firstRow hs i ∨
      (packedRectangleCorner hs choice (i, s)).1 = RectanglePacking.secondRow hs i := by
  fin_cases s <;> simp [packedRectangleCorner]

/-- The whole joint rectangle packing uses at most two cells in every row. -/
theorem packedRectangleSupport_row_load {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (r : Fin n) :
    (LayerPacking.rowUsed (packedRectangleSupport hs choice) r).card ≤ 2 := by
  classical
  by_cases hex : ∃ i : Fin L, ∃ side : Fin 4, (packedRectangleCorner hs choice (i, side)).1 = r
  · obtain ⟨i, s, hr⟩ := hex
    have hsub : LayerPacking.rowUsed (packedRectangleSupport hs choice) r ⊆
        {RectanglePacking.firstColumn hs choice i, RectanglePacking.secondColumn hs choice i} := by
      intro c hc
      have hcell : (r, c) ∈ packedRectangleSupport hs choice := by simpa [LayerPacking.rowUsed] using hc
      obtain ⟨⟨j, t⟩, _, heq⟩ := Finset.mem_image.mp hcell
      have hrows : (packedRectangleCorner hs choice (j, t)).1 =
          (packedRectangleCorner hs choice (i, s)).1 := by rw [heq, hr]
      have hji := packedCorner_row_label hs choice j i t s hrows
      subst j
      have hcols := packedCorner_column_cases hs choice i t
      rw [heq] at hcols
      simpa using hcols
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · have hempty : LayerPacking.rowUsed (packedRectangleSupport hs choice) r = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c hc
      have hcell : (r, c) ∈ packedRectangleSupport hs choice := by simpa [LayerPacking.rowUsed] using hc
      obtain ⟨⟨j, t⟩, _, heq⟩ := Finset.mem_image.mp hcell
      exact hex ⟨j, t, congrArg Prod.fst heq⟩
    simp [hempty]

/-- The whole joint rectangle packing also uses at most two cells in every column. -/
theorem packedRectangleSupport_column_load {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (c : Fin n) :
    (LayerPacking.colUsed (packedRectangleSupport hs choice) c).card ≤ 2 := by
  classical
  by_cases hex : ∃ i : Fin L, ∃ side : Fin 4, (packedRectangleCorner hs choice (i, side)).2 = c
  · obtain ⟨i, s, hc⟩ := hex
    have hsub : LayerPacking.colUsed (packedRectangleSupport hs choice) c ⊆
        {RectanglePacking.firstRow hs i, RectanglePacking.secondRow hs i} := by
      intro r hr
      have hcell : (r, c) ∈ packedRectangleSupport hs choice := by simpa [LayerPacking.colUsed] using hr
      obtain ⟨⟨j, t⟩, _, heq⟩ := Finset.mem_image.mp hcell
      have hcols : (packedRectangleCorner hs choice (j, t)).2 =
          (packedRectangleCorner hs choice (i, s)).2 := by rw [heq, hc]
      have hji := packedCorner_column_label hs choice j i t s hcols
      subst j
      have hrows := packedCorner_row_cases hs choice i t
      rw [heq] at hrows
      simpa using hrows
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · have hempty : LayerPacking.colUsed (packedRectangleSupport hs choice) c = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      have hcell : (r, c) ∈ packedRectangleSupport hs choice := by simpa [LayerPacking.colUsed] using hr
      obtain ⟨⟨j, t⟩, _, heq⟩ := Finset.mem_image.mp hcell
      exact hex ⟨j, t, congrArg Prod.snd heq⟩
    simp [hempty]

/-- Reserving any subset of the packed rectangles increases each existing
row and column load by at most the source's two-cell rectangle allowance. -/
theorem packedRectangleSupport_union_load {L n B : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (base added : Finset (Cell n))
    (hadded : added ⊆ packedRectangleSupport hs choice)
    (hrow : ∀ r, (LayerPacking.rowUsed base r).card ≤ B)
    (hcol : ∀ c, (LayerPacking.colUsed base c).card ≤ B) :
    (∀ r, (LayerPacking.rowUsed (base ∪ added) r).card ≤ B + 2) ∧
      (∀ c, (LayerPacking.colUsed (base ∪ added) c).card ≤ B + 2) := by
  have hrowAdded : ∀ r, (LayerPacking.rowUsed added r).card ≤ 2 := by
    intro r
    apply (Finset.card_le_card ?_).trans (packedRectangleSupport_row_load hs choice r)
    intro c hc
    have h := (Finset.mem_filter.mp hc).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadded h⟩
  have hcolAdded : ∀ c, (LayerPacking.colUsed added c).card ≤ 2 := by
    intro c
    apply (Finset.card_le_card ?_).trans (packedRectangleSupport_column_load hs choice c)
    intro r hr
    have h := (Finset.mem_filter.mp hr).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadded h⟩
  constructor
  · intro r
    rw [LayerPacking.rowUsed_union]
    have h := Finset.card_union_le (LayerPacking.rowUsed base r) (LayerPacking.rowUsed added r)
    have hb := hrow r
    have ha := hrowAdded r
    omega
  · intro c
    rw [LayerPacking.colUsed_union]
    have h := Finset.card_union_le (LayerPacking.colUsed base c) (LayerPacking.colUsed added c)
    have hb := hcol c
    have ha := hcolAdded c
    omega

/-- Previously installed and newly added rectangles are charged jointly:
the same RP1 packing contributes at most two cells per line in total,
even when the previous reservation already contains other rectangles. -/
theorem packedRectangle_joint_reservation_load {L n B : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (base ordinary added : Finset (Cell n))
    (hbase : base ⊆ ordinary ∪ packedRectangleSupport hs choice)
    (hadded : added ⊆ packedRectangleSupport hs choice)
    (hrow : ∀ r, (LayerPacking.rowUsed ordinary r).card ≤ B)
    (hcol : ∀ c, (LayerPacking.colUsed ordinary c).card ≤ B) :
    (∀ r, (LayerPacking.rowUsed (base ∪ added) r).card ≤ B + 2) ∧
      (∀ c, (LayerPacking.colUsed (base ∪ added) c).card ≤ B + 2) := by
  have hsub : base ∪ added ⊆ ordinary ∪ packedRectangleSupport hs choice := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hbase hz
    · exact Finset.mem_union_right _ (hadded hz)
  have hbound := packedRectangleSupport_union_load hs choice ordinary
    (packedRectangleSupport hs choice) (Finset.Subset.rfl) hrow hcol
  constructor
  · intro r
    apply (Finset.card_le_card ?_).trans (hbound.1 r)
    intro c hc
    have hcell := (Finset.mem_filter.mp hc).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub hcell⟩
  · intro c
    apply (Finset.card_le_card ?_).trans (hbound.2 c)
    intro r hr
    have hcell := (Finset.mem_filter.mp hr).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub hcell⟩

end
end Sude
