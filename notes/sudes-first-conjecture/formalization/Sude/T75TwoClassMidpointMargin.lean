import Sude.T75ConditionalSelection
namespace Sude
noncomputable section

/-- Distinct narrow and wide coordinate families supply T75's midpoint margin,
with a nonnegative D/4 surplus under the stated one-coordinate slack. This
proves neither endpoints prime nor existence of the step grid. -/
theorem t75_two_class_midpoint_margin_with_slack {β : Type*} [DecidableEq β]
    (narrow wide : Finset β) (low gap : β → ℕ) (y D : ℝ) (hD : 0 ≤ D)
    (hdis : Disjoint narrow wide) (hcount : 2*narrow.card+5 ≤ wide.card)
    (hnarrow : ∀ i ∈ narrow, |(low i : ℝ) + (gap i : ℝ)/2 - y| ≤ D/2)
    (hwide : ∀ i ∈ wide, |(low i : ℝ) + (gap i : ℝ)/2 - y| ≤ D/4)
    (hgap : ∀ i ∈ wide, D ≤ (gap i : ℝ)) :
    |((∑ i ∈ narrow ∪ wide, low i : ℕ) : ℝ) +
      ((∑ i ∈ narrow ∪ wide, gap i : ℕ) : ℝ)/2 - ((narrow ∪ wide).card : ℝ)*y| + D + D/4 ≤
      ((∑ i ∈ narrow ∪ wide, gap i : ℕ) : ℝ)/2 := by
  classical
  let f : β → ℝ := fun i => (low i : ℝ) + (gap i : ℝ)/2 - y
  have hN : |∑ i ∈ narrow, f i| ≤ (narrow.card : ℝ)*(D/2) := by
    have ha := Finset.abs_sum_le_sum_abs f narrow
    have hb : (∑ i ∈ narrow, |f i|) ≤ ∑ _i ∈ narrow, D/2 :=
      Finset.sum_le_sum (fun i hi => hnarrow i hi)
    simpa using ha.trans hb
  have hW : |∑ i ∈ wide, f i| ≤ (wide.card : ℝ)*(D/4) := by
    have ha := Finset.abs_sum_le_sum_abs f wide
    have hb : (∑ i ∈ wide, |f i|) ≤ ∑ _i ∈ wide, D/4 :=
      Finset.sum_le_sum (fun i hi => hwide i hi)
    simpa using ha.trans hb
  have hsum : ((∑ i ∈ narrow ∪ wide, low i : ℕ) : ℝ) +
      ((∑ i ∈ narrow ∪ wide, gap i : ℕ) : ℝ)/2 - ((narrow ∪ wide).card : ℝ)*y =
      (∑ i ∈ narrow, f i) + (∑ i ∈ wide, f i) := by
    rw [Finset.sum_union hdis, Finset.sum_union hdis, Finset.card_union_of_disjoint hdis]
    simp only [Nat.cast_add, Nat.cast_sum]
    dsimp [f]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul]
    ring_nf
    simp only [← Finset.sum_mul]
    ring
  have hmid : |((∑ i ∈ narrow ∪ wide, low i : ℕ) : ℝ) +
      ((∑ i ∈ narrow ∪ wide, gap i : ℕ) : ℝ)/2 - ((narrow ∪ wide).card : ℝ)*y| ≤
      (narrow.card : ℝ)*(D/2) + (wide.card : ℝ)*(D/4) := by
    rw [hsum]
    have ha := abs_add_le (∑ i ∈ narrow, f i) (∑ i ∈ wide, f i)
    linarith
  have hgapW : (wide.card : ℝ)*D ≤ ∑ i ∈ wide, (gap i : ℝ) := by
    simpa using Finset.sum_le_sum (s := wide) (fun i hi => hgap i hi)
  have hgapN : (0 : ℝ) ≤ ∑ i ∈ narrow, (gap i : ℝ) := Finset.sum_nonneg (fun i hi => Nat.cast_nonneg _)
  have hgapAll : (wide.card : ℝ)*D ≤ ((∑ i ∈ narrow ∪ wide, gap i : ℕ) : ℝ) := by
    rw [Finset.sum_union hdis, Nat.cast_add, Nat.cast_sum, Nat.cast_sum]
    linarith
  have hc : (2 : ℝ)*(narrow.card : ℝ)+5 ≤ (wide.card : ℝ) := by exact_mod_cast hcount
  have hm := mul_nonneg (show 0 ≤ (wide.card : ℝ) - 2*(narrow.card : ℝ) - 5 by linarith) hD
  nlinarith [hmid, hgapAll]

/-- Exact `hmargin` field used by `t75_conditional_step_selection`. -/
theorem t75_two_class_hmargin {β : Type*} [DecidableEq β]
    (narrow wide : Finset β) (low gap : β → ℕ) (y D : ℝ) (hD : 0 ≤ D)
    (hdis : Disjoint narrow wide) (hcount : 2*narrow.card+5 ≤ wide.card)
    (hnarrow : ∀ i ∈ narrow, |(low i : ℝ) + (gap i : ℝ)/2 - y| ≤ D/2)
    (hwide : ∀ i ∈ wide, |(low i : ℝ) + (gap i : ℝ)/2 - y| ≤ D/4)
    (hgap : ∀ i ∈ wide, D ≤ (gap i : ℝ)) :
    |((∑ i ∈ narrow ∪ wide, low i : ℕ) : ℝ) +
      ((∑ i ∈ narrow ∪ wide, gap i : ℕ) : ℝ)/2 - ((narrow ∪ wide).card : ℝ)*y| + D ≤
      ((∑ i ∈ narrow ∪ wide, gap i : ℕ) : ℝ)/2 := by
  have h := t75_two_class_midpoint_margin_with_slack narrow wide low gap y D hD hdis hcount hnarrow hwide hgap
  linarith

end
end Sude
