import Sude.PrefixSelectionBudget

/-! Strict PD6 budget when the common width is positive. -/
namespace Sude
noncomputable section

/-- The two successive remaining-mean corrections preserve a strict
`3C/2` total discrepancy budget when `C` is positive. -/
theorem prefix_three_selection_budget_strict (n C E1 eps2 eps3 : ℝ)
    (hn : 0 ≤ n) (hC : 0 < C)
    (h1 : |E1| ≤ C/2) (h2 : |eps2| ≤ C/2) (h3 : |eps3| ≤ C/2) :
    |(n/(n+4))*(((n+4)/(n+6))*E1 + eps2) + eps3| < (3/2)*C := by
  have hn4 : 0 < n+4 := by linarith
  have hn6 : 0 < n+6 := by linarith
  have hr : 0 ≤ n/(n+4) := by positivity
  have hrlt : n/(n+4) < 1 := (div_lt_one hn4).2 (by linarith)
  have htlt : (n+5)/(n+6) < 1 := (div_lt_one hn6).2 (by linarith)
  have hE : |((n+4)/(n+6))*E1 + eps2| ≤ ((n+5)/(n+6))*C :=
    (prefix_three_selection_budget n C E1 eps2 eps3 hn (le_of_lt hC) h1 h2 h3).2.1
  have hElt : |((n+4)/(n+6))*E1 + eps2| < C := by
    have := mul_lt_mul_of_pos_right htlt hC
    nlinarith
  have hE_le : |((n+4)/(n+6))*E1 + eps2| ≤ C := le_of_lt hElt
  have hbound : |(n/(n+4))*(((n+4)/(n+6))*E1 + eps2) + eps3| ≤
      (n/(n+4))*C + C/2 := by
    calc
      _ ≤ |(n/(n+4))*(((n+4)/(n+6))*E1 + eps2)| + |eps3| := abs_add_le _ _
      _ = (n/(n+4))*|((n+4)/(n+6))*E1 + eps2| + |eps3| := by
        rw [abs_mul, abs_of_nonneg hr]
      _ ≤ (n/(n+4))*C + C/2 := add_le_add (mul_le_mul_of_nonneg_left hE_le hr) h3
  have := mul_lt_mul_of_pos_right hrlt hC
  nlinarith

end
end Sude
