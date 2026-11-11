import Mathlib.Tactic

/-! Arithmetic for the three labelled selections of the prefix construction. -/
namespace Sude
noncomputable section

theorem prefix_three_selection_natural_arithmetic (n d : ℕ) (hn : 3 ≤ n) (hd : 2 ≤ d) :
    let M := d * (n + 8)
    let r := 2 * d
    let q := 4 * d
    r ≤ M ∧ r ≤ M-r ∧ q ≤ M-(r+r) ∧
    0 < M-r ∧ 0 < M-(r+r) ∧
    M-r = d*(n+6) ∧ M-(r+r) = d*(n+4) := by
  dsimp
  have h₁ : d * (n + 8) - 2 * d = d * (n + 6) := by
    simp only [Nat.mul_add]
    omega
  have h₂ : d * (n + 8) - (2 * d + 2 * d) = d * (n + 4) := by
    simp only [Nat.mul_add]
    omega
  constructor
  · simp only [Nat.mul_add]; omega
  constructor
  · rw [h₁]; simp only [Nat.mul_add]; omega
  constructor
  · rw [h₂]; simp only [Nat.mul_add]; omega
  constructor
  · rw [h₁]; positivity
  constructor
  · rw [h₂]; positivity
  exact ⟨h₁, h₂⟩

theorem prefix_three_selection_real_ratios (n d : ℕ) (hn : 3 ≤ n) (hd : 2 ≤ d) :
    ((2*d : ℕ) : ℝ) / (((d*(n+8) - 2*d : ℕ) : ℝ)) = 2/((n : ℝ)+6) ∧
    ((4*d : ℕ) : ℝ) / (((d*(n+8) - (2*d+2*d) : ℕ) : ℝ)) = 4/((n : ℝ)+4) := by
  have h := prefix_three_selection_natural_arithmetic n d hn hd
  dsimp only at h
  obtain ⟨_, _, _, _, _, h₁, h₂⟩ := h
  rw [h₁, h₂]
  push_cast
  have hdn : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hn6 : (n : ℝ)+6 ≠ 0 := by positivity
  have hn4 : (n : ℝ)+4 ≠ 0 := by positivity
  constructor <;> field_simp

/-- Factors in the two cumulative-discrepancy recurrences. -/
theorem prefix_three_selection_weight_identities (n : ℕ) :
    1 - 2 / ((n : ℝ) + 6) = ((n : ℝ) + 4) / ((n : ℝ) + 6) ∧
    1 - 4 / ((n : ℝ) + 4) = (n : ℝ) / ((n : ℝ) + 4) := by
  have hn6 : (n : ℝ)+6 ≠ 0 := by positivity
  have hn4 : (n : ℝ)+4 ≠ 0 := by positivity
  constructor <;> field_simp <;> ring

end
end Sude
