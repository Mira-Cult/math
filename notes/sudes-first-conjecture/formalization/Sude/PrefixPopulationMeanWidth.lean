import Sude.CentralWindow

/-! A labelled population's mean lies within its value-width of every member.
No selection, physical allocation, or line bound is asserted. -/
namespace Sude
noncomputable section

/-- For a finite labelled population whose ordered differences are at most
`C`, each member differs from the actual population mean by at most `C`.
The labels remain distinct even when numerical values coincide. -/
theorem prefix_population_member_mean_width {α : Type*} (A : Finset α)
    (x : α → ℝ) (C : ℝ)
    (hwidth : ∀ a ∈ A, ∀ b ∈ A, x b - x a ≤ C)
    (a : α) (ha : a ∈ A) :
    |x a - (∑ b ∈ A, x b) / A.card| ≤ C := by
  classical
  have hp : (0 : ℝ) < A.card := by exact_mod_cast (Finset.card_pos.mpr ⟨a, ha⟩)
  have hsumlo : (x a - C) * (A.card : ℝ) ≤ ∑ b ∈ A, x b := by
    calc
      _ = ∑ _b ∈ A, (x a - C) := by simp [mul_comm, sub_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro b hb
        have h := hwidth b hb a ha
        linarith
  have hsumhi : (∑ b ∈ A, x b) ≤ (x a + C) * (A.card : ℝ) := by
    calc
      _ ≤ ∑ _b ∈ A, (x a + C) := by
        apply Finset.sum_le_sum
        intro b hb
        have h := hwidth a ha b hb
        linarith
      _ = _ := by simp [mul_comm, add_mul]
  have hlo : x a - C ≤ (∑ b ∈ A, x b) / A.card := (le_div_iff₀ hp).2 hsumlo
  have hhi : (∑ b ∈ A, x b) / A.card ≤ x a + C := (div_le_iff₀ hp).2 hsumhi
  rw [abs_le]
  constructor <;> linarith

end
end Sude
