import Sude.MatchedBinDepletedPairs

/-! Convert FW's global deletion and gap-span bounds to the exact square gate. -/
namespace Sude
noncomputable section

/-- Paying an upper bound on the shared deletion set and an upper bound on
the gap-label population implies the matched-bin square gate. The natural
subtractions are truncated explicitly, including when the budget exceeds the
initial stock. -/
theorem matched_bin_square_gate_of_budget {N W B X : ℕ} (removed differences : Finset ℕ)
    (hrem : removed.card ≤ B) (hspan : differences.card ≤ X)
    (hgate : (N : ℝ) * X < ((N * W - B : ℕ) : ℝ) ^ 2) :
    (N : ℝ) * differences.card < ((N * W - removed.card : ℕ) : ℝ) ^ 2 := by
  have hsub : N * W - B ≤ N * W - removed.card := Nat.sub_le_sub_left hrem _
  have hsubR : ((N * W - B : ℕ) : ℝ) ≤ ((N * W - removed.card : ℕ) : ℝ) := by exact_mod_cast hsub
  have hnon : 0 ≤ ((N * W - B : ℕ) : ℝ) := by positivity
  have hsquare : ((N * W - B : ℕ) : ℝ) ^ 2 ≤
      ((N * W - removed.card : ℕ) : ℝ) ^ 2 := by nlinarith
  have hspanR : (differences.card : ℝ) ≤ X := by exact_mod_cast hspan
  have hN : 0 ≤ (N : ℝ) := by positivity
  exact (mul_le_mul_of_nonneg_left hspanR hN).trans_lt (hgate.trans_le hsquare)

end
end Sude
