import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Arithmetic for the two successive aggregate mean-shift invoices in
PD3--PD4. These estimates require their exact algebraic identities as inputs. -/
namespace Sude
noncomputable section

private theorem abs_linear_budget (r x y A B : ℝ) (hr : 0 ≤ r)
    (hx : |x| ≤ A) (hy : |y| ≤ B) : |r*x + y| ≤ r*A + B := by
  calc
    |r*x + y| ≤ |r*x| + |y| := abs_add_le _ _
    _ = r*|x| + |y| := by rw [abs_mul, abs_of_nonneg hr]
    _ ≤ r*A + B := add_le_add (mul_le_mul_of_nonneg_left hx hr) hy

/-- The PD3/PD4 scalar invoices given the exact successive mean shifts and
three aggregate selection errors. This does not construct the selections. -/
theorem prefix_three_selection_budget (n C E1 eps2 eps3 : ℝ)
    (hn : 0 ≤ n) (hC : 0 ≤ C)
    (h1 : |E1| ≤ C/2) (h2 : |eps2| ≤ C/2) (h3 : |eps3| ≤ C/2) :
    |-(2/(n+6))*E1 + eps2| ≤ ((n+8)/(2*(n+6)))*C ∧
    |((n+4)/(n+6))*E1 + eps2| ≤ ((n+5)/(n+6))*C ∧
    |(n/(n+4))*(((n+4)/(n+6))*E1 + eps2) + eps3| ≤ (3/2)*C := by
  have hn4 : 0 < n+4 := by linarith
  have hn6 : 0 < n+6 := by linarith
  have hneg : 0 ≤ 2/(n+6) := by positivity
  have hr2 : 0 ≤ (n+4)/(n+6) := by positivity
  have hr3 : 0 ≤ n/(n+4) := by positivity
  have hr2le : (n+4)/(n+6) ≤ 1 := (div_le_one hn6).2 (by linarith)
  have hr3le : n/(n+4) ≤ 1 := (div_le_one hn4).2 (by linarith)
  have hD := abs_linear_budget (2/(n+6)) (-E1) eps2 (C/2) (C/2) hneg (by simpa using h1) h2
  have hE := abs_linear_budget ((n+4)/(n+6)) E1 eps2 (C/2) (C/2) hr2 h1 h2
  have hD' : (2/(n+6))*(C/2) + C/2 = ((n+8)/(2*(n+6)))*C := by field_simp; ring
  have hE' : ((n+4)/(n+6))*(C/2) + C/2 = ((n+5)/(n+6))*C := by field_simp; ring
  have hEbound : |((n+4)/(n+6))*E1 + eps2| ≤ C := by
    have ht := mul_le_mul_of_nonneg_right hr2le (show 0 ≤ C/2 by positivity)
    linarith
  have hthird := abs_linear_budget (n/(n+4)) (((n+4)/(n+6))*E1 + eps2) eps3 C (C/2) hr3 hEbound h3
  have ht := mul_le_mul_of_nonneg_right hr3le hC
  constructor
  · rw [← hD']; simpa only [mul_neg, neg_mul] using hD
  constructor
  · rw [← hE']; exact hE
  · linarith

end
end Sude
