import Sude.RegularFactorRF2
/-! RF2 completion with the exact global exception count retained separately
from the local exception degree. -/
namespace Sude
noncomputable section

theorem central_exception_mean_shift_exact_count {α : Type*} [DecidableEq α]
    (unused chosen : Finset α) (value : α → ℝ) (k n T : ℕ) (radius : ℝ)
    (hsub : chosen ⊆ unused) (hk : 0 < k) (hn : 0 < n) (_hrad : 0 ≤ radius)
    (hrest : (unused \ chosen).card = k * n) (hcount : chosen.card = T)
    (hnear : ∀ x ∈ chosen, |value x - centralEntriesMean unused value| ≤ radius) :
    |(k : ℝ) * (centralEntriesMean (unused \ chosen) value - centralEntriesMean unused value)| ≤
      ((T : ℝ) / n) * radius := by
  classical
  let μ := centralEntriesMean unused value
  let D := (∑ x ∈ chosen, value x) - (chosen.card : ℝ) * μ
  have hD : |D| ≤ (T : ℝ) * radius := by
    have hsum : |∑ x ∈ chosen, (value x - μ)| ≤ ∑ x ∈ chosen, |value x - μ| :=
      Finset.abs_sum_le_sum_abs _ _
    have hterm : (∑ x ∈ chosen, |value x - μ|) ≤ ∑ _x ∈ chosen, radius := by
      apply Finset.sum_le_sum
      intro x hx
      exact hnear x hx
    have heq : (∑ x ∈ chosen, (value x - μ)) = D := by
      simp [D, Finset.sum_sub_distrib]
    rw [heq] at hsum
    simpa [hcount] using hsum.trans hterm
  have hpos : 0 < (unused \ chosen).card := by rw [hrest]; exact Nat.mul_pos hk hn
  have hupdate := central_entries_actual_mean_update unused chosen value hsub hpos
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : (k : ℝ) * (centralEntriesMean (unused \ chosen) value - μ) = -D / (n : ℝ) := by
    rw [hupdate, hrest]
    push_cast
    dsimp [D, μ]
    field_simp
    ring
  rw [heq, abs_div, abs_neg, abs_of_pos hnreal]
  have hb := div_le_div_of_nonneg_right hD hnreal.le
  have hcalc : ((T : ℝ) * radius) / n = ((T : ℝ) / n) * radius := by ring
  rw [← hcalc]
  exact hb

theorem central_exception_line_error_exact_count
    (factorSum exceptionSum μ μf k m X t radius : ℝ) (T n : ℕ)
    (hf : |factorSum - k * μf| < X)
    (he : |exceptionSum - m * μ| ≤ t * radius)
    (hm : |k * (μf - μ)| ≤ ((T : ℝ) / n) * radius) :
    |factorSum + exceptionSum - (k + m) * μ| <
      X + (t + (T : ℝ) / n) * radius := by
  have htriangle := abs_add_le (factorSum - k * μf) (exceptionSum - m * μ + k * (μf - μ))
  have htriangle₂ := abs_add_le (exceptionSum - m * μ) (k * (μf - μ))
  have hid : factorSum + exceptionSum - (k + m) * μ =
      (factorSum - k * μf) + (exceptionSum - m * μ + k * (μf - μ)) := by ring
  rw [hid]
  nlinarith

theorem central_stock_regular_factor_completion_exact_count {n k t : ℕ}
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
            centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| < X + ((t : ℝ) + (((Finset.univ \ reserved) \ E).card : ℝ) / n) * radius) ∧
      (∀ c, |(columnSum b c : ℝ) -
        ((∑ z ∈ columnCells c ∩ reserved, (entry a z : ℝ)) +
          ((columnCells c \ reserved).card : ℝ) *
            centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| < X + ((t : ℝ) + (((Finset.univ \ reserved) \ E).card : ℝ) / n) * radius) ∧
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
  have hmean := central_exception_mean_shift_exact_count (actualUnusedPool a reserved) chosen centralPoolValue
    k n exc.card radius hsub hk hn hrad hrest hc hnear
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
    have hcomb := central_exception_line_error_exact_count
      ((rowSum b r : ℝ) - fixed - extra) extra μ μf k (rowCells r ∩ exc).card X t radius exc.card n
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
    have hcomb := central_exception_line_error_exact_count
      ((columnSum b c : ℝ) - fixed - extra) extra μ μf k (columnCells c ∩ exc).card X t radius exc.card n
      hfactor hextra hmean
    have hcount := factor_line_free_card reserved E (columnCells c) hE
    rw [factor_column_cells_card, hreg.2 c] at hcount
    have hcountR : ((columnCells c \ reserved).card : ℝ) = (k : ℝ) + (columnCells c ∩ exc).card := by
      exact_mod_cast hcount
    rw [hcountR]
    convert hcomb using 1; dsimp [fixed, extra, μ]; ring_nf

end
end Sude
