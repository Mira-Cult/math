import Sude.CentralWindow

/-! Cardinal bounds on the active equations in one joint prefix-rounding
step. These lemmas do not construct a rounding step. -/
namespace Sude
noncomputable section

/-- An occupied group cannot have exactly one fractional variable if its
fractional entries sum to an integer. This premise follows from an integral
group total when all other slots have been frozen at zero or one. -/
theorem prefix_integer_fractional_group_has_two {S G : Type*} [DecidableEq G]
    (F : Finset S) (group : S → G) (x : S → ℝ)
    (hx : ∀ s ∈ F, 0 < x s ∧ x s < 1)
    (hint : ∀ g ∈ F.image group, ∃ z : ℤ,
      (∑ s ∈ F.filter (fun s => group s = g), x s) = z) :
    ∀ g ∈ F.image group, 2 ≤ (F.filter (fun s => group s = g)).card := by
  classical
  intro g hg
  obtain ⟨s, hs, hsg⟩ := Finset.mem_image.mp hg
  let B := F.filter (fun s => group s = g)
  have hsB : s ∈ B := Finset.mem_filter.mpr ⟨hs, hsg⟩
  have hpos : 0 < B.card := Finset.card_pos.mpr ⟨s, hsB⟩
  by_contra hn
  change ¬ 2 ≤ B.card at hn
  have hone : B.card = 1 := by omega
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hone
  obtain ⟨z, hz⟩ := hint g hg
  change (∑ s ∈ B, x s) = z at hz
  rw [ht] at hz hsB
  simp only [Finset.sum_singleton] at hz
  have htF : t ∈ F := (Finset.mem_filter.mp (by rw [ht]; simp : t ∈ B)).1
  obtain ⟨hlo, hhi⟩ := hx t htF
  rw [hz] at hlo hhi
  have hz0 : (0 : ℤ) < z := by exact_mod_cast hlo
  have hz1 : z < (1 : ℤ) := by exact_mod_cast hhi
  omega

/-- If each occupied group has at least two fractional slots, then there are
at most half as many occupied groups as fractional slots. -/
theorem prefix_fractional_group_count {S G : Type*} [DecidableEq G]
    (F : Finset S) (group : S → G)
    (hpair : ∀ g ∈ F.image group, 2 ≤ (F.filter (fun s => group s = g)).card) :
    2 * (F.image group).card ≤ F.card := by
  classical
  have hc := Finset.card_eq_sum_card_fiberwise (s := F) (t := F.image group)
    (f := group) (by intro s hs; exact Finset.mem_image_of_mem group hs)
  have hsum : ∑ g ∈ F.image group, 2 ≤
      ∑ g ∈ F.image group, (F.filter (fun s => group s = g)).card := by
    exact Finset.sum_le_sum hpair
  rw [hc]
  simpa [Nat.mul_comm] using hsum

/-- Strictly retained line equations have fewer than half as many members as
fractional slots when `C > 0`, using the global per-slot mass budget. -/
theorem prefix_retained_line_count {S L : Type*}
    (F : Finset S) (R : Finset L) (a : L → S → ℝ) (C : ℝ)
    (hC : 0 < C) (hF : F.Nonempty)
    (hrow : ∀ l ∈ R, 10 * C < ∑ s ∈ F, a l s)
    (hcol : ∀ s ∈ F, (∑ l ∈ R, a l s) ≤ 5 * C) :
    2 * R.card < F.card := by
  classical
  by_cases hR : R.Nonempty
  · have hl := Finset.sum_lt_sum_of_nonempty hR hrow
    have hu : (∑ l ∈ R, ∑ s ∈ F, a l s) ≤ ∑ s ∈ F, 5 * C := by
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum hcol
    have hn : ((R.card : ℝ) * (10 * C)) < (F.card : ℝ) * (5 * C) := by
      simpa using lt_of_lt_of_le hl hu
    have hcard : (2 * R.card : ℝ) < F.card := by nlinarith
    exact_mod_cast hcard
  · have hR0 : R.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hR)
    have hF0 : 0 < F.card := Finset.card_pos.mpr hF
    omega

/-- In the zero-width case no line can remain above the drop threshold:
nonnegative coefficients and zero per-slot mass force every retained entry
to vanish. -/
theorem prefix_zero_width_no_retained_lines {S L : Type*}
    (F : Finset S) (R : Finset L) (a : L → S → ℝ)
    (hnonneg : ∀ l ∈ R, ∀ s ∈ F, 0 ≤ a l s)
    (hrow : ∀ l ∈ R, 0 < ∑ s ∈ F, a l s)
    (hcol : ∀ s ∈ F, (∑ l ∈ R, a l s) ≤ 0) : R = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro l hl
  have hz : ∀ s ∈ F, a l s = 0 := by
    intro s hs
    have hb : a l s ≤ ∑ l' ∈ R, a l' s :=
      Finset.single_le_sum (fun l' hl' => hnonneg l' hl' s hs) hl
    have hlower := hnonneg l hl s hs
    have hupper := hcol s hs
    linarith
  have heq : (∑ s ∈ F, a l s) = 0 := Finset.sum_eq_zero hz
  have hpos := hrow l hl
  linarith

/-- Under these two counting hypotheses there are strictly fewer retained
active group and line equations than fractional variables. -/
theorem prefix_rounding_equation_count {S G L : Type*} [DecidableEq G]
    (F : Finset S) (group : S → G) (R : Finset L) (a : L → S → ℝ) (C : ℝ)
    (hC : 0 < C) (hF : F.Nonempty)
    (hpair : ∀ g ∈ F.image group, 2 ≤ (F.filter (fun s => group s = g)).card)
    (hrow : ∀ l ∈ R, 10 * C < ∑ s ∈ F, a l s)
    (hcol : ∀ s ∈ F, (∑ l ∈ R, a l s) ≤ 5 * C) :
    (F.image group).card + R.card < F.card := by
  have hg := prefix_fractional_group_count F group hpair
  have hl := prefix_retained_line_count F R a C hC hF hrow hcol
  omega


/-- Full DP2 dimension count, including zero width. Integer fractional-group
sums and strict fractionality imply the occupied-group bound; retained lines
are counted jointly across all groups and stages. -/
theorem prefix_rounding_integral_equations_count {S G L : Type*} [DecidableEq G]
    (F : Finset S) (group : S → G) (R : Finset L) (x : S → ℝ)
    (a : L → S → ℝ) (C : ℝ) (hC : 0 ≤ C) (hF : F.Nonempty)
    (hx : ∀ s ∈ F, 0 < x s ∧ x s < 1)
    (hint : ∀ g ∈ F.image group, ∃ z : ℤ,
      (∑ s ∈ F.filter (fun s => group s = g), x s) = z)
    (hnonneg : ∀ l ∈ R, ∀ s ∈ F, 0 ≤ a l s)
    (hrow : ∀ l ∈ R, 10 * C < ∑ s ∈ F, a l s)
    (hcol : ∀ s ∈ F, (∑ l ∈ R, a l s) ≤ 5 * C) :
    (F.image group).card + R.card < F.card := by
  classical
  have hpair := prefix_integer_fractional_group_has_two F group x hx hint
  rcases lt_or_eq_of_le hC with hpos | hzero
  · exact prefix_rounding_equation_count F group R a C hpos hF hpair hrow hcol
  · have heq : C = 0 := hzero.symm
    have hrow' : ∀ l ∈ R, 0 < ∑ s ∈ F, a l s := by simpa [heq] using hrow
    have hcol' : ∀ s ∈ F, (∑ l ∈ R, a l s) ≤ 0 := by simpa [heq] using hcol
    have hR : R = ∅ := prefix_zero_width_no_retained_lines F R a hnonneg hrow' hcol'
    have hg := prefix_fractional_group_count F group hpair
    have hFpos : 0 < F.card := Finset.card_pos.mpr hF
    rw [hR]
    simp only [Finset.card_empty, add_zero]
    omega

end
end Sude
