import Sude.BMORPoolScalarMean

/-!
Finite rational gate for the FW mean estimate. These inequalities only
certify algebraic cell endpoints; their analytic hypotheses and link to the
actual pool mean are separate obligations.
-/
namespace Sude
noncomputable section

/-- BG's lower count coefficient, written without the leading `1/u`. -/
def fwMeanA (u : ℝ) : ℝ := 1 + 1/u + 2/u^2 + 6/u^3

/-- BG's upper count coefficient, written without the leading `1/u`. -/
def fwMeanB (u : ℝ) : ℝ := 1 + 1/u + 4/u^2

/-- Exact rational bounds on each width-1/8 cell of [181/8, 29]. -/
theorem fw_mean_rational_cells (i : ℕ) (hi : i < 51) :
    let a : ℝ := (181 + (i : ℝ)) / 8
    let b : ℝ := (182 + (i : ℝ)) / 8
    let c : ℝ := (281649 / 62500 : ℝ) / 65536
    let W : ℝ := 2^32
    0 < fwMeanA b - c ∧
      (243 / 500 : ℝ) < (fwMeanA (2*b) / 2 - 2*c - 4*b/W^2) / (fwMeanB a + c) ∧
      (fwMeanB (2*a) / 2 + 2*c + fwMeanB a/W) / (fwMeanA b - c) < (123 / 250 : ℝ) := by
  have hbound : i ≤ 50 := by omega
  interval_cases i <;> norm_num [fwMeanA, fwMeanB]

end
end Sude
