import Sude.FWFirstBandLogScoreBounds

/-! A numerical comparison for a proposed active-diagonal invoice. This file
does not prove the component estimates or construct a witness, grid, or prime. -/
namespace Sude
noncomputable section

/-- The proposed bridge, wide, gap, growth, seed and spare constants fit
within `27 * X`. The quotient `n / 450` is natural division. -/
theorem fw_first_band_active_diagonal_numeric_invoice {n : ℕ} {X : ℝ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hX : 100 ≤ X) :
    let k := ((n / 450 : ℕ) : ℝ)
    let B := X * (23 / 924 : ℝ) * Real.sqrt (94 * Real.log (8 * (n : ℝ) + 8))
    let W := X * (2 / 235 : ℝ) * Real.sqrt ((54 * k + 4) * Real.log (8 * (n : ℝ) + 8))
    let E := Real.sqrt ((3 / 2 : ℝ) * (3 * k) * ((64 / 235 : ℝ) * X)^2 * Real.log 16)
    3 * X + 2 * B + (613256873 / 949132107 : ℝ) * X + 2 * W + 2 * E +
      (((n : ℝ) + 7) / (6 * ((n : ℝ) + 6))) * X + (7 / 2 : ℝ) * X < 27 * X := by
  dsimp only
  have hk : ((n / 450 : ℕ) : ℝ) ≤ 47 := by exact_mod_cast (show n / 450 ≤ 47 by omega)
  have hk0 : (0 : ℝ) ≤ ((n / 450 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hx0 : 0 ≤ X := by linarith
  have hb := fw_first_band_bridge_sqrt_le_35 (by omega : n ≤ 35733)
  have hw := fw_first_band_wide_sqrt_le_183 hnhi
  have hlog : Real.log (16 : ℝ) < 3 := by
    have heq : (16 : ℝ) = 2 ^ 4 := by norm_num
    rw [heq, Real.log_pow]
    have h := Real.log_two_lt_d9
    norm_num at h ⊢
    linarith
  have hlog0 : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  have hs : Real.sqrt ((9 / 2 : ℝ) * ((n / 450 : ℕ) : ℝ) * Real.log 16) ≤ 26 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · have hm : ((n / 450 : ℕ) : ℝ) * Real.log 16 ≤ 47 * 3 := by
        exact mul_le_mul hk (le_of_lt hlog) hlog0 (by norm_num)
      nlinarith
  have heq : Real.sqrt ((3 / 2 : ℝ) * (3 * ((n / 450 : ℕ) : ℝ)) *
        ((64 / 235 : ℝ) * X)^2 * Real.log 16) =
      ((64 / 235 : ℝ) * X) * Real.sqrt ((9 / 2 : ℝ) * ((n / 450 : ℕ) : ℝ) * Real.log 16) := by
    have hfac : (3 / 2 : ℝ) * (3 * ((n / 450 : ℕ) : ℝ)) *
        ((64 / 235 : ℝ) * X)^2 * Real.log 16 =
        ((64 / 235 : ℝ) * X)^2 * ((9 / 2 : ℝ) * ((n / 450 : ℕ) : ℝ) * Real.log 16) := by ring
    rw [hfac, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg (by norm_num) hx0)]
  rw [heq]
  have hn : (19485 : ℝ) ≤ n := by exact_mod_cast hnlo
  have hden : 0 < 6 * ((n : ℝ) + 6) := by linarith
  have hg : ((n : ℝ) + 7) / (6 * ((n : ℝ) + 6)) ≤ (1 / 6 : ℝ) + 1 / 100000 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hbg : X * (23 / 924 : ℝ) * Real.sqrt (94 * Real.log (8 * (n : ℝ) + 8)) ≤ X * (23 / 924 : ℝ) * 35 :=
    mul_le_mul_of_nonneg_left hb (mul_nonneg hx0 (by norm_num))
  have hwg : X * (2 / 235 : ℝ) * Real.sqrt ((54 * ((n / 450 : ℕ) : ℝ) + 4) * Real.log (8 * (n : ℝ) + 8)) ≤ X * (2 / 235 : ℝ) * 183 :=
    mul_le_mul_of_nonneg_left hw (mul_nonneg hx0 (by norm_num))
  have heg := mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64 / 235) hx0)
  have hgg := mul_le_mul_of_nonneg_right hg hx0
  nlinarith

/-- The basic grid capacity dominates the same scalar budget; no grid is
constructed here. -/
theorem fw_first_band_active_diagonal_capacity {n X : ℕ}
    (hnlo : 19485 ≤ n) (hX : 100 ≤ X) :
    (27 : ℝ) * X ≤ ((4 * (((n / 450) * X) / 2) : ℕ) : ℝ) := by
  have hk : 43 ≤ n / 450 := by omega
  have hprod : 43 * X ≤ (n / 450) * X := Nat.mul_le_mul_right X hk
  have hround : (n / 450) * X ≤ 2 * (((n / 450) * X) / 2) + 1 := by omega
  have hp : (43 : ℝ) * X ≤ ((n / 450) * X : ℕ) := by exact_mod_cast hprod
  have hr : (((n / 450) * X : ℕ) : ℝ) ≤ 2 * (((n / 450) * X / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hround
  have hx : (100 : ℝ) ≤ X := by exact_mod_cast hX
  push_cast
  nlinarith

/-- Across `19485 ≤ n ≤ 35733`, the bridge, wide, gap, growth, seed and spare
constants fit within `32 * X`. -/
theorem fw_all_bands_active_diagonal_numeric_invoice {n : ℕ} {X : ℝ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hX : 100 ≤ X) :
    let k := ((n / 450 : ℕ) : ℝ)
    let B := X * (23 / 924 : ℝ) * Real.sqrt (94 * Real.log (8 * (n : ℝ) + 8))
    let W := X * (2 / 235 : ℝ) * Real.sqrt ((54 * k + 4) * Real.log (8 * (n : ℝ) + 8))
    let E := Real.sqrt ((3 / 2 : ℝ) * (3 * k) * ((64 / 235 : ℝ) * X)^2 * Real.log 16)
    3 * X + 2 * B + (613256873 / 949132107 : ℝ) * X + 2 * W + 2 * E +
      (((n : ℝ) + 7) / (6 * ((n : ℝ) + 6))) * X + (7 / 2 : ℝ) * X < 32 * X := by
  dsimp only
  have hk : ((n / 450 : ℕ) : ℝ) ≤ 79 := by exact_mod_cast (show n / 450 ≤ 79 by omega)
  have hk0 : (0 : ℝ) ≤ ((n / 450 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hx0 : 0 ≤ X := by linarith
  have hb := fw_first_band_bridge_sqrt_le_35 hnhi
  have hw := fw_wide_sqrt_le_236 hnhi
  have hlog : Real.log (16 : ℝ) < 3 := by
    have heq : (16 : ℝ) = 2 ^ 4 := by norm_num
    rw [heq, Real.log_pow]
    have h := Real.log_two_lt_d9
    norm_num at h ⊢
    linarith
  have hlog0 : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  have hs : Real.sqrt ((9 / 2 : ℝ) * ((n / 450 : ℕ) : ℝ) * Real.log 16) ≤ 33 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · have hm : ((n / 450 : ℕ) : ℝ) * Real.log 16 ≤ 79 * 3 := by
        exact mul_le_mul hk (le_of_lt hlog) hlog0 (by norm_num)
      nlinarith
  have heq : Real.sqrt ((3 / 2 : ℝ) * (3 * ((n / 450 : ℕ) : ℝ)) *
        ((64 / 235 : ℝ) * X)^2 * Real.log 16) =
      ((64 / 235 : ℝ) * X) * Real.sqrt ((9 / 2 : ℝ) * ((n / 450 : ℕ) : ℝ) * Real.log 16) := by
    have hfac : (3 / 2 : ℝ) * (3 * ((n / 450 : ℕ) : ℝ)) *
        ((64 / 235 : ℝ) * X)^2 * Real.log 16 =
        ((64 / 235 : ℝ) * X)^2 * ((9 / 2 : ℝ) * ((n / 450 : ℕ) : ℝ) * Real.log 16) := by ring
    rw [hfac, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg (by norm_num) hx0)]
  rw [heq]
  have hn : (19485 : ℝ) ≤ n := by exact_mod_cast hnlo
  have hden : 0 < 6 * ((n : ℝ) + 6) := by linarith
  have hg : ((n : ℝ) + 7) / (6 * ((n : ℝ) + 6)) ≤ (1 / 6 : ℝ) + 1 / 100000 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hbg : X * (23 / 924 : ℝ) * Real.sqrt (94 * Real.log (8 * (n : ℝ) + 8)) ≤ X * (23 / 924 : ℝ) * 35 :=
    mul_le_mul_of_nonneg_left hb (mul_nonneg hx0 (by norm_num))
  have hwg : X * (2 / 235 : ℝ) * Real.sqrt ((54 * ((n / 450 : ℕ) : ℝ) + 4) * Real.log (8 * (n : ℝ) + 8)) ≤ X * (2 / 235 : ℝ) * 236 :=
    mul_le_mul_of_nonneg_left hw (mul_nonneg hx0 (by norm_num))
  have heg := mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64 / 235) hx0)
  have hgg := mul_le_mul_of_nonneg_right hg hx0
  nlinarith

end
end Sude
