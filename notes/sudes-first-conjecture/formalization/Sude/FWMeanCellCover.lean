import Sude.FWMeanRationalCells

namespace Sude

/-- The 51 closed rational cells cover the exact logarithmic FW interval. -/
theorem fw_mean_cells_cover {u : ℝ} (hlo : (181 / 8 : ℝ) ≤ u)
    (hhi : u ≤ 29) :
    ∃ i : ℕ, i < 51 ∧ (181 + (i : ℝ)) / 8 ≤ u ∧ u ≤ (182 + (i : ℝ)) / 8 := by
  by_cases hlast : u = 29
  · subst u
    refine ⟨50, by decide, ?_, ?_⟩ <;> norm_num
  · have hlt : u < 29 := lt_of_le_of_ne hhi hlast
    let z : ℝ := 8*u - 181
    have hz : 0 ≤ z := by dsimp [z]; linarith
    have hzupper : z < 51 := by dsimp [z]; linarith
    let i : ℕ := ⌊z⌋₊
    have hil : (i : ℝ) ≤ z := Nat.floor_le hz
    have hiu : z < (i : ℝ) + 1 := Nat.lt_floor_add_one z
    have hi : i < 51 := by
      have h : (i : ℝ) < 51 := lt_of_le_of_lt hil hzupper
      exact_mod_cast h
    refine ⟨i, hi, ?_, ?_⟩ <;> dsimp [z] at * <;> linarith

end Sude
