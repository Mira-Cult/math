import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Exact mean-change accounting for three central batches. -/
namespace Sude

/-- CC10's signed identity, retaining the changing mean before each batch.
The later stock sizes are positive and differ by the actual selected counts. -/
theorem central_three_error_identity
    (N₁ N₂ N₃ q₁ q₂ μ₀ μ₁ μ₂ e₀ e₁ e₂ : ℝ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hcount₁ : N₁ = N₂ + q₁) (hcount₂ : N₂ = N₃ + q₂)
    (hmean₁ : μ₁ = μ₀ - e₀ / N₁) (hmean₂ : μ₂ = μ₁ - e₁ / N₂) :
    e₀ + (e₁ + q₁ * (μ₁ - μ₀)) + (e₂ + q₂ * (μ₂ - μ₀)) =
      e₀ * (N₃ / N₁) + e₁ * (N₃ / N₂) + e₂ := by
  subst μ₂
  subst μ₁
  subst N₁
  subst N₂
  have hne₁ : N₃ + q₂ + q₁ ≠ 0 := ne_of_gt hN₁
  have hne₂ : N₃ + q₂ ≠ 0 := ne_of_gt hN₂
  field_simp
  ring

/-- Each error keeps its own weight in `[0,1]`; their combined signed
deviation is bounded by three batch allowances. -/
theorem central_three_weighted_errors (η e₀ e₁ e₂ w₀ w₁ : ℝ)
    (hη : 0 ≤ η) (he₀ : |e₀| ≤ η) (he₁ : |e₁| ≤ η) (he₂ : |e₂| ≤ η)
    (hw₀ : 0 ≤ w₀ ∧ w₀ ≤ 1) (hw₁ : 0 ≤ w₁ ∧ w₁ ≤ 1) :
    |e₀ * w₀ + e₁ * w₁ + e₂| ≤ 3 * η := by
  have h₀ : |e₀ * w₀| ≤ η := by
    rw [abs_mul, abs_of_nonneg hw₀.1]
    calc
      |e₀| * w₀ ≤ η * w₀ := mul_le_mul_of_nonneg_right he₀ hw₀.1
      _ ≤ η := by nlinarith
  have h₁ : |e₁ * w₁| ≤ η := by
    rw [abs_mul, abs_of_nonneg hw₁.1]
    calc
      |e₁| * w₁ ≤ η * w₁ := mul_le_mul_of_nonneg_right he₁ hw₁.1
      _ ≤ η := by nlinarith
  have htriangle := abs_add_le (e₀ * w₀ + e₁ * w₁) e₂
  have htriangle' := abs_add_le (e₀ * w₀) (e₁ * w₁)
  linarith

/-- The exact CC10 identity and positive remaining counts imply the signed
three-batch deviation bound `3 * η`. -/
theorem central_three_error_bound
    (N₁ N₂ N₃ q₁ q₂ μ₀ μ₁ μ₂ e₀ e₁ e₂ η : ℝ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hN₃ : 0 ≤ N₃)
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hcount₁ : N₁ = N₂ + q₁) (hcount₂ : N₂ = N₃ + q₂)
    (hmean₁ : μ₁ = μ₀ - e₀ / N₁) (hmean₂ : μ₂ = μ₁ - e₁ / N₂)
    (hη : 0 ≤ η) (he₀ : |e₀| ≤ η) (he₁ : |e₁| ≤ η) (he₂ : |e₂| ≤ η) :
    |e₀ + (e₁ + q₁ * (μ₁ - μ₀)) + (e₂ + q₂ * (μ₂ - μ₀))| ≤ 3 * η := by
  rw [central_three_error_identity N₁ N₂ N₃ q₁ q₂ μ₀ μ₁ μ₂ e₀ e₁ e₂
    hN₁ hN₂ hcount₁ hcount₂ hmean₁ hmean₂]
  apply central_three_weighted_errors η e₀ e₁ e₂ (N₃ / N₁) (N₃ / N₂) hη he₀ he₁ he₂
  · constructor
    · positivity
    · exact (div_le_one hN₁).2 (by linarith)
  · constructor
    · positivity
    · exact (div_le_one hN₂).2 (by linarith)

end Sude
