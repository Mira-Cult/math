import Sude.CentralWindow

/-! Mean bounds for two finite labelled populations. This does not choose
sorted halves, prove a rounding result, or construct an allocation. -/
namespace Sude
noncomputable section

/-- If every value in the first nonempty labelled population is at most
every value in the second, their means are ordered. Labels need not have
distinct numerical values. -/
theorem prefix_finite_means_le {A B : Type*} (P : Finset A) (Q : Finset B)
    (x : A → ℝ) (y : B → ℝ) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hxy : ∀ i ∈ P, ∀ j ∈ Q, x i ≤ y j) :
    (∑ i ∈ P, x i) / P.card ≤ (∑ j ∈ Q, y j) / Q.card := by
  classical
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr hP
  have hQpos : (0 : ℝ) < Q.card := by exact_mod_cast Finset.card_pos.mpr hQ
  apply (div_le_div_iff₀ hPpos hQpos).2
  calc
    (∑ i ∈ P, x i) * (Q.card : ℝ) = ∑ i ∈ P, ∑ j ∈ Q, x i := by
      simp [Finset.sum_mul, mul_comm]
    _ ≤ ∑ i ∈ P, ∑ j ∈ Q, y j := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum (fun j hj => hxy i hi j hj)
    _ = (∑ j ∈ Q, y j) * (P.card : ℝ) := by
      rw [Finset.sum_comm]
      simp [Finset.sum_mul, mul_comm]

/-- For nonempty lower and upper labelled populations, all cross-pair gaps
in `[0,C]` imply their mean gap also lies in `[0,C]`. -/
theorem prefix_finite_split_mean_gap {A B : Type*} (P : Finset A) (Q : Finset B)
    (x : A → ℝ) (y : B → ℝ) (C : ℝ) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hxy : ∀ i ∈ P, ∀ j ∈ Q, 0 ≤ y j - x i ∧ y j - x i ≤ C) :
    0 ≤ (∑ j ∈ Q, y j) / Q.card - (∑ i ∈ P, x i) / P.card ∧
      (∑ j ∈ Q, y j) / Q.card - (∑ i ∈ P, x i) / P.card ≤ C := by
  classical
  have hlower := prefix_finite_means_le P Q x y hP hQ (by
    intro i hi j hj
    linarith [(hxy i hi j hj).1])
  have hupper := prefix_finite_means_le Q P y (fun i => x i + C) hQ hP (by
    intro j hj i hi
    linarith [(hxy i hi j hj).2])
  have hPne : (P.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr hP))
  have hsum : (∑ i ∈ P, (x i + C)) / P.card = (∑ i ∈ P, x i) / P.card + C := by
    rw [Finset.sum_add_distrib]
    simp [add_div, hPne]
  rw [hsum] at hupper
  exact ⟨by linarith, by linarith⟩

end
end Sude
