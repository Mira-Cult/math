import Sude.BGActualMeanLower

/-! Exact numerical gates for using the weaker aggregate odd-prime error
1367/250 on the BG range. These lemmas do not establish a count estimate. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- The BG first cell remains above 0.487 with the theta-repair coefficient
once the stronger BG-specific square-root floor is used. -/
theorem bg_theta_mean_first_cell_gate :
    let a : ℝ := 24
    let b : ℝ := 385 / 16
    let c : ℝ := (1367 / 250 : ℝ) / 131072
    let W : ℝ := 2^32
    0 < fwMeanA b - c ∧
      (487 / 1000 : ℝ) < (fwMeanA (2*b)/2 - 2*c - 4*b/W^2)/(fwMeanB a+c) := by
  norm_num [fwMeanA, fwMeanB]

/-- The existing shifted BG cells retain their stronger lower-mean gate. -/
theorem bg_theta_mean_shifted_cell_gates (i : ℕ) (hi : i < 40) :
    let a : ℝ := (385 + 2*(i : ℝ))/16
    let b : ℝ := (387 + 2*(i : ℝ))/16
    let c : ℝ := (1367 / 250 : ℝ) / 131072
    let W : ℝ := 2^32
    0 < fwMeanA b - c ∧
      (487 / 1000 : ℝ) < (fwMeanA (2*b)/2 - 2*c - 4*b/W^2)/(fwMeanB a+c) := by
  have hbound : i ≤ 39 := by omega
  interval_cases i <;> norm_num [fwMeanA, fwMeanB]

/-- The 51 existing FW logarithm cells remain valid with the aggregate
1367/250 count error and the original 65536 square-root floor. -/
theorem fw_theta_mean_rational_cells (i : ℕ) (hi : i < 51) :
    let a : ℝ := (181 + (i : ℝ)) / 8
    let b : ℝ := (182 + (i : ℝ)) / 8
    let c : ℝ := (1367 / 250 : ℝ) / 65536
    let W : ℝ := 2^32
    0 < fwMeanA b - c ∧
      (243 / 500 : ℝ) < (fwMeanA (2*b) / 2 - 2*c - 4*b/W^2) / (fwMeanB a + c) ∧
      (fwMeanB (2*a) / 2 + 2*c + fwMeanB a/W) / (fwMeanA b - c) < (123 / 250 : ℝ) := by
  have hbound : i ≤ 50 := by omega
  interval_cases i <;> norm_num [fwMeanA, fwMeanB]

/-- The FW index-ratio rational gate also survives the weaker count error. -/
theorem fw_theta_index_ratio_rational_gate {u : ℝ}
    (hlo : (181 / 8 : ℝ) ≤ u) (hhi : u ≤ 29) :
    (u - 9/8) * (fwMeanB u + (1367 / 250 : ℝ) / 65536) < u := by
  let c : ℝ := (1367 / 250 : ℝ) / 65536
  have hu : 0 < u := by linarith
  have h1 : (23 / 8 : ℝ) / u ≤ (23 / 8 : ℝ) / (181 / 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlo
  have h2 : (9 / 2 : ℝ) / 29^2 ≤ (9 / 2 : ℝ) / u^2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hu 2)
      (pow_le_pow_left₀ hu.le hhi 2)
  have h3 : c * (u - 9 / 8) ≤ c * (29 - 9 / 8) := by
    apply mul_le_mul_of_nonneg_left (by linarith)
    dsimp [c]; norm_num
  have hnum : (0 : ℝ) < 1/8 - (23/8)/(181/8) + (9/2)/29^2 - c*(29-9/8) := by
    dsimp [c]; norm_num
  have hid : u - (u - 9/8) * (fwMeanB u + c) =
      1/8 - (23/8)/u + (9/2)/u^2 - c*(u-9/8) := by
    dsimp [fwMeanB]
    field_simp
    ring
  rw [← sub_pos, hid]
  linarith

end
end Sude
