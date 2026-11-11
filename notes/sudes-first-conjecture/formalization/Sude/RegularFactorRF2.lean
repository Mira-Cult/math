import Sude.RegularFactorMeanShift

/-! Physical accounting for the RF2 central-exception completion. -/
namespace Sude
noncomputable section

/-- Any subset of centrally placed exceptional cells has the expected
bounded deviation from the original pool mean. -/
theorem central_exception_cells_error {n : ℕ} (a a₁ : Cell n ≃ Fin (n * n))
    (reserved exc line : Finset (Cell n)) (chosen : Finset (pool n))
    (radius : ℝ) (t : ℕ) (hrad : 0 ≤ radius)
    (hchosen : chosen ⊆ centralExceptionStock a reserved radius)
    (himage : exc.image (entry a₁) = chosen.image Subtype.val)
    (hcount : (line ∩ exc).card ≤ t) :
    |(∑ z ∈ line ∩ exc, (entry a₁ z : ℝ)) -
      ((line ∩ exc).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
        (t : ℝ) * radius := by
  classical
  let μ := centralEntriesMean (actualUnusedPool a reserved) centralPoolValue
  have hpoint : ∀ z ∈ line ∩ exc, |(entry a₁ z : ℝ) - μ| ≤ radius := by
    intro z hz
    have hm : entry a₁ z ∈ chosen.image Subtype.val := by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨z, (Finset.mem_inter.mp hz).2, rfl⟩
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hm
    have hvnear := (Finset.mem_filter.mp (hchosen hv)).2
    simpa [centralPoolValue, μ, ← heq] using hvnear
  have hs : |∑ z ∈ line ∩ exc, ((entry a₁ z : ℝ) - μ)| ≤
      ∑ z ∈ line ∩ exc, |(entry a₁ z : ℝ) - μ| := Finset.abs_sum_le_sum_abs _ _
  have ht : (∑ z ∈ line ∩ exc, |(entry a₁ z : ℝ) - μ|) ≤
      ∑ _z ∈ line ∩ exc, radius := Finset.sum_le_sum hpoint
  have hc : ((line ∩ exc).card : ℝ) ≤ t := by exact_mod_cast hcount
  have hmul := mul_le_mul_of_nonneg_right hc hrad
  simp only [Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul] at hs ht
  dsimp [μ] at hs ht
  linarith

/-- Counting factor cells in a row agrees with the row degree of the
bipartite support. -/
theorem factor_row_cells_card {n : ℕ} (E : Finset (Cell n)) (r : Fin n) :
    (rowCells r ∩ E).card = (LayerPacking.rowUsed E r).card := by
  classical
  have heq : rowCells r ∩ E = (LayerPacking.rowUsed E r).image (fun j => (r, j)) := by
    ext ⟨i, j⟩
    simp [rowCells, LayerPacking.rowUsed, Prod.ext_iff, and_comm, eq_comm]
    aesop
  rw [heq, Finset.card_image_of_injective]
  intro i j h
  exact congrArg Prod.snd h

/-- The analogous identity for columns. -/
theorem factor_column_cells_card {n : ℕ} (E : Finset (Cell n)) (c : Fin n) :
    (columnCells c ∩ E).card = (LayerPacking.colUsed E c).card := by
  classical
  have heq : columnCells c ∩ E = (LayerPacking.colUsed E c).image (fun i => (i, c)) := by
    ext ⟨i, j⟩
    simp [columnCells, LayerPacking.colUsed, Prod.ext_iff, and_comm, eq_comm]
    aesop
  rw [heq, Finset.card_image_of_injective]
  intro i j h
  exact congrArg Prod.fst h

/-- A free line splits into factor cells and exceptional cells. -/
theorem factor_line_free_card {n : ℕ} (reserved E line : Finset (Cell n))
    (hE : E ⊆ Finset.univ \ reserved) :
    (line \ reserved).card = (line ∩ E).card +
      (line ∩ ((Finset.univ \ reserved) \ E)).card := by
  classical
  have hset : line \ reserved = (line ∩ E) ∪ (line ∩ ((Finset.univ \ reserved) \ E)) := by
    ext z
    have hE' : z ∈ E → z ∉ reserved := fun hz => (Finset.mem_sdiff.mp (hE hz)).2
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, Finset.mem_univ, true_and]
    by_cases hzE : z ∈ E <;> aesop
  rw [hset, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hz').2).2 (Finset.mem_inter.mp hz).2

/-- The fixed contribution splits into its original reservation and its
newly installed exceptional cells. -/
theorem factor_line_fixed_sum {n : ℕ} (a a₁ : Cell n ≃ Fin (n * n))
    (reserved exc line : Finset (Cell n)) (hdisj : Disjoint reserved exc)
    (hfixed : ∀ z ∈ reserved, entry a₁ z = entry a z) :
    (∑ z ∈ line ∩ (reserved ∪ exc), (entry a₁ z : ℝ)) =
      (∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
        ∑ z ∈ line ∩ exc, (entry a₁ z : ℝ) := by
  classical
  rw [Finset.inter_union_distrib_left, Finset.sum_union]
  · congr 1
    apply Finset.sum_congr rfl
    intro z hz
    rw [hfixed z (Finset.mem_inter.mp hz).2]
  · apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact Finset.disjoint_left.mp hdisj (Finset.mem_inter.mp hz).2 (Finset.mem_inter.mp hz').2

/-- The per-row exception limit implies the total deletion budget. -/
theorem exception_budget_of_row_degrees {n t : ℕ} (exc : Finset (Cell n))
    (hrow : ∀ r : Fin n, (rowCells r ∩ exc).card ≤ t) : exc.card ≤ t * n := by
  classical
  have hfiber : exc.card = ∑ r : Fin n, (rowCells r ∩ exc).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := exc) (t := Finset.univ)
      (f := fun z : Cell n => z.1) (by intro z hz; simp)
    convert h using 1
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    ext z
    simp [mem_rowCells, and_comm]
  rw [hfiber]
  have h := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin n))) => hrow r)
  simpa [Nat.mul_comm] using h

/-- RF2's physical completion, conditional on an actual regular factor and
central stock. The total exception budget is derived from the row degree bounds. -/
theorem central_stock_regular_factor_completion {n k t : ℕ}
    (a : Cell n ≃ Fin (n * n)) (reserved E : Finset (Cell n))
    (hE : E ⊆ Finset.univ \ reserved) (hreg : CellFactorRegular E k)
    (hk : 0 < k) (hn : 0 < n)
    (hmain : mainCells n ⊆ reserved) (hanti : antiCells n ⊆ reserved)
    (X radius : ℝ) (hrad : 0 ≤ radius)
    (hwidth : ∀ u ∈ actualUnusedPool a reserved, ∀ v ∈ actualUnusedPool a reserved,
      (u.val : ℝ) - (v.val : ℝ) < X)
    (hstock : ((Finset.univ \ reserved) \ E).card ≤
      (centralExceptionStock a reserved radius).card)
    (hrow : ∀ r, (rowCells r ∩ ((Finset.univ \ reserved) \ E)).card ≤ t)
    (hcol : ∀ c, (columnCells c ∩ ((Finset.univ \ reserved) \ E)).card ≤ t) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      (∀ r, |(rowSum b r : ℝ) -
        ((∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)) +
          ((rowCells r \ reserved).card : ℝ) *
            centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| < X + 2 * t * radius) ∧
      (∀ c, |(columnSum b c : ℝ) -
        ((∑ z ∈ columnCells c ∩ reserved, (entry a z : ℝ)) +
          ((columnCells c \ reserved).card : ℝ) *
            centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| < X + 2 * t * radius) ∧
      mainSum b = mainSum a ∧ antiSum b = antiSum a ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  classical
  let exc := (Finset.univ \ reserved) \ E
  obtain ⟨chosen, a₁, b, hchosen, hc, himage, hfixed, hpool, hfixb,
      hbrow, hbcol, hm, ha, hp, hinj⟩ :=
    place_central_exceptions_and_complete_factor a reserved E hE hreg hk hn hmain hanti X radius hwidth hstock
  have hdisj : Disjoint reserved exc := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz').1).2 hz
  have hfree : E = Finset.univ \ (reserved ∪ exc) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, exc]
    constructor
    · intro hz
      have hzfree := Finset.mem_sdiff.mp (hE hz)
      simp [hzfree.2, hz]
    · intro hz
      by_contra he
      exact hz (Or.inr ⟨fun hr => hz (Or.inl hr), he⟩)
  obtain ⟨ps, hlen, _, hcard, _, _, _, _, _, _, _⟩ :=
    place_sorted_regular_factor a₁ (reserved ∪ exc) E hfree hreg
  have hrest : (actualUnusedPool a reserved \ chosen).card = k * n := by
    rw [← hpool]
    simpa [hlen] using hcard
  have hsub : chosen ⊆ actualUnusedPool a reserved := by
    intro v hv
    exact (Finset.mem_filter.mp (hchosen hv)).1
  have hnear : ∀ v ∈ chosen,
      |centralPoolValue v - centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤ radius := by
    intro v hv
    exact (Finset.mem_filter.mp (hchosen hv)).2
  have hbudget := exception_budget_of_row_degrees exc hrow
  have hmean := central_exception_mean_shift (actualUnusedPool a reserved) chosen centralPoolValue
    k n t radius hsub hk hn hrad hrest (by simpa [hc] using hbudget) hnear
  refine ⟨b, ?_, ?_, ?_, hm, ha, hp, hinj⟩
  · intro z hz
    exact (hfixb z (Finset.mem_union_left _ hz)).trans (hfixed z hz)
  · intro r
    let fixed := ∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)
    let extra := ∑ z ∈ rowCells r ∩ exc, (entry a₁ z : ℝ)
    let μ := centralEntriesMean (actualUnusedPool a reserved) centralPoolValue
    let μf := centralEntriesMean (actualUnusedPool a reserved \ chosen) centralPoolValue
    have hsplit := factor_line_fixed_sum a a₁ reserved exc (rowCells r) hdisj hfixed
    have hfactor : |((rowSum b r : ℝ) - fixed - extra) - (k : ℝ) * μf| < X := by
      have hh := hbrow r
      rw [hsplit] at hh
      convert hh using 1; dsimp [fixed, extra, μf]; ring_nf
    have hextra : |extra - ((rowCells r ∩ exc).card : ℝ) * μ| ≤ (t : ℝ) * radius :=
      central_exception_cells_error a a₁ reserved exc (rowCells r) chosen radius t hrad hchosen himage (hrow r)
    have hcomb := central_exception_line_error
      ((rowSum b r : ℝ) - fixed - extra) extra μ μf k (rowCells r ∩ exc).card X t radius
      hfactor hextra hmean
    have hcount := factor_line_free_card reserved E (rowCells r) hE
    rw [factor_row_cells_card, hreg.1 r] at hcount
    have hcountR : ((rowCells r \ reserved).card : ℝ) = (k : ℝ) + (rowCells r ∩ exc).card := by
      exact_mod_cast hcount
    rw [hcountR]
    convert hcomb using 1; dsimp [fixed, extra, μ]; ring_nf
  · intro c
    let fixed := ∑ z ∈ columnCells c ∩ reserved, (entry a z : ℝ)
    let extra := ∑ z ∈ columnCells c ∩ exc, (entry a₁ z : ℝ)
    let μ := centralEntriesMean (actualUnusedPool a reserved) centralPoolValue
    let μf := centralEntriesMean (actualUnusedPool a reserved \ chosen) centralPoolValue
    have hsplit := factor_line_fixed_sum a a₁ reserved exc (columnCells c) hdisj hfixed
    have hfactor : |((columnSum b c : ℝ) - fixed - extra) - (k : ℝ) * μf| < X := by
      have hh := hbcol c
      rw [hsplit] at hh
      convert hh using 1; dsimp [fixed, extra, μf]; ring_nf
    have hextra : |extra - ((columnCells c ∩ exc).card : ℝ) * μ| ≤ (t : ℝ) * radius :=
      central_exception_cells_error a a₁ reserved exc (columnCells c) chosen radius t hrad hchosen himage (hcol c)
    have hcomb := central_exception_line_error
      ((columnSum b c : ℝ) - fixed - extra) extra μ μf k (columnCells c ∩ exc).card X t radius
      hfactor hextra hmean
    have hcount := factor_line_free_card reserved E (columnCells c) hE
    rw [factor_column_cells_card, hreg.2 c] at hcount
    have hcountR : ((columnCells c \ reserved).card : ℝ) = (k : ℝ) + (columnCells c ∩ exc).card := by
      exact_mod_cast hcount
    rw [hcountR]
    convert hcomb using 1; dsimp [fixed, extra, μ]; ring_nf

end
end Sude
