import Sude.CentralAccounting

/-! Scalar error bounds for the two labelled diagonals in CC3. -/
namespace Sude

/-- The two labelled diagonal errors retain the common center and the
appropriate mean shifts before each noncentral batch. -/
theorem central_diagonal_error_identities
    (N₁ N₂ q₁ q₂ μ₀ μ₁ μ₂ e₀ e₁ e₂ : ℝ)
    (hmean₁ : μ₁ = μ₀ - e₀ / N₁) (hmean₂ : μ₂ = μ₁ - e₁ / N₂) :
    e₀ + e₁ + q₁ * (μ₁ - μ₀) = e₀ * (1 - q₁ / N₁) + e₁ ∧
      e₀ + e₂ + q₂ * (μ₂ - μ₀) =
        e₀ * (1 - q₂ / N₁) - (q₂ / N₂) * e₁ + e₂ := by
  subst μ₂
  subst μ₁
  constructor <;> ring

theorem central_weighted_abs (e w η : ℝ) (he : |e| ≤ η) (hw : 0 ≤ w) :
    |e * w| ≤ η * w := by
  rw [abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_right he hw

/-- The two CC3 error formulas, including the common center and both mean
shifts, obey the source's diagonal bounds under its ratio inequality. -/
theorem central_diagonal_scalar_bounds
    (N₁ N₂ q₁ q₂ e₀ e₁ e₂ η : ℝ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hcount : N₁ = N₂ + q₁) (hq₂N : q₂ ≤ N₂)
    (hratio : q₁ * q₂ / (N₁ * N₂) ≤ 1 / 100)
    (hη : 0 ≤ η) (he₀ : |e₀| ≤ η) (he₁ : |e₁| ≤ η) (he₂ : |e₂| ≤ η) :
    |e₀ * (1 - q₁ / N₁) + e₁| ≤ 2 * η ∧
      |e₀ * (1 - q₂ / N₁) - (q₂ / N₂) * e₁ + e₂| ≤ (201 / 100) * η := by
  have hq₁N : q₁ ≤ N₁ := by linarith
  have hq₂N₁ : q₂ ≤ N₁ := by linarith
  have hw₁ : 0 ≤ 1 - q₁ / N₁ ∧ 1 - q₁ / N₁ ≤ 1 := by
    have hq : 0 ≤ q₁ / N₁ := div_nonneg hq₁ hN₁.le
    have hq' : q₁ / N₁ ≤ 1 := (div_le_one hN₁).2 hq₁N
    constructor <;> linarith
  have hw₂ : 0 ≤ 1 - q₂ / N₁ := by
    have hq : q₂ / N₁ ≤ 1 := (div_le_one hN₁).2 hq₂N₁
    linarith
  have hw₃ : 0 ≤ q₂ / N₂ := div_nonneg hq₂ hN₂.le
  have hcoef : (1 - q₂ / N₁) + q₂ / N₂ + 1 = 2 + q₁ * q₂ / (N₁ * N₂) := by
    subst N₁
    have hne₁ : N₂ + q₁ ≠ 0 := ne_of_gt hN₁
    have hne₂ : N₂ ≠ 0 := ne_of_gt hN₂
    field_simp
    ring
  have hfirst := central_weighted_abs e₀ (1 - q₁ / N₁) η he₀ hw₁.1
  have hsecond := central_weighted_abs e₀ (1 - q₂ / N₁) η he₀ hw₂
  have hthird : |(q₂ / N₂) * e₁| ≤ η * (q₂ / N₂) := by
    simpa [mul_comm] using central_weighted_abs e₁ (q₂ / N₂) η he₁ hw₃
  constructor
  · have ht := abs_add_le (e₀ * (1 - q₁ / N₁)) e₁
    have hm := mul_le_mul_of_nonneg_left hw₁.2 hη
    nlinarith
  · have ht := abs_add_le (e₀ * (1 - q₂ / N₁) - (q₂ / N₂) * e₁) e₂
    have ht' : |e₀ * (1 - q₂ / N₁) - (q₂ / N₂) * e₁| ≤
        |e₀ * (1 - q₂ / N₁)| + |(q₂ / N₂) * e₁| := by
      simpa [sub_eq_add_neg] using abs_add_le (e₀ * (1 - q₂ / N₁)) (-((q₂ / N₂) * e₁))
    have hr := mul_le_mul_of_nonneg_left hratio hη
    have hc := congrArg (fun x : ℝ => η * x) hcoef
    nlinarith

/-- The source's `n ≥ 20`, `Nᵢ ≥ 7n²/10` and `qᵢ ≤ n` bounds certify the
small ratio used by CC3, without numerical floating-point evaluation. -/
theorem central_diagonal_source_ratio (n N₁ N₂ q₁ q₂ : ℝ)
    (hn : 20 ≤ n) (hq₁ : 0 ≤ q₁ ∧ q₁ ≤ n) (hq₂ : 0 ≤ q₂ ∧ q₂ ≤ n)
    (hN₁ : (7 / 10) * n ^ 2 ≤ N₁) (hN₂ : (7 / 10) * n ^ 2 ≤ N₂) :
    0 < N₁ ∧ 0 < N₂ ∧ q₂ ≤ N₂ ∧ q₁ * q₂ / (N₁ * N₂) ≤ 1 / 100 := by
  have hn0 : 0 ≤ n := by linarith
  have hn2 : 400 ≤ n ^ 2 := by nlinarith
  have hN₁pos : 0 < N₁ := by nlinarith
  have hN₂pos : 0 < N₂ := by nlinarith
  have hq₂N : q₂ ≤ N₂ := by nlinarith
  have hqprod : q₁ * q₂ ≤ n * n := mul_le_mul hq₁.2 hq₂.2 hq₂.1 hn0
  have hbase : (0 : ℝ) ≤ (7 / 10) * n ^ 2 := by positivity
  have hprod : ((7 / 10) * n ^ 2) * ((7 / 10) * n ^ 2) ≤ N₁ * N₂ :=
    mul_le_mul hN₁ hN₂ hbase (by linarith)
  have hquad : 100 * (n * n) ≤ ((7 / 10) * n ^ 2) * ((7 / 10) * n ^ 2) := by
    have h := mul_nonneg (show 0 ≤ n ^ 2 by positivity) (show 0 ≤ n ^ 2 - 400 by linarith)
    nlinarith [h]
  refine ⟨hN₁pos, hN₂pos, hq₂N, ?_⟩
  apply (div_le_iff₀ (mul_pos hN₁pos hN₂pos)).2
  nlinarith

/-- CC1's original count and the first diagonal's size imply the two
denominator bounds used in CC3. -/
theorem central_diagonal_source_denominators (n N N₁ N₂ q₁ : ℕ)
    (hn : 20 ≤ n) (hN : 3 * n * n ≤ 4 * N) (hq₁ : q₁ ≤ n - 1)
    (hc₁ : N₁ + 1 = N) (hc₂ : N₂ + q₁ = N₁) :
    7 * n * n ≤ 10 * N₁ ∧ 7 * n * n ≤ 10 * N₂ := by
  have hq₁' : q₁ + 1 ≤ n := by omega
  have hquad : 20 * n ≤ n * n := by nlinarith
  have hN' : 3 * (n * n) ≤ 4 * N := by simpa only [mul_assoc] using hN
  have hgoal : 7 * (n * n) ≤ 10 * N₁ ∧ 7 * (n * n) ≤ 10 * N₂ := by omega
  simpa only [mul_assoc] using hgoal

end Sude
