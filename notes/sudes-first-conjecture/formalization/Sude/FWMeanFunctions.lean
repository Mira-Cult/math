import Sude.FWMeanRationalCells

/-! Monotonicity and cell bounds for the scaled BG functions used in the
finite-window pool mean estimate. No numerical prime-count input is assumed. -/
namespace Sude
noncomputable section

/-- Connection with the existing normalized lower count expression. -/
theorem fwMeanA_eq_scaled {u : ℝ} (hu : u ≠ 0) :
    fwMeanA u = u * bgLiLowerNorm u := by
  simp only [fwMeanA, bgLiLowerNorm]
  field_simp

/-- Connection with the existing normalized upper count expression. -/
theorem fwMeanB_eq_scaled {u : ℝ} (hu : u ≠ 0) :
    fwMeanB u = u * bgLiUpperNorm u := by
  simp only [fwMeanB, bgLiUpperNorm]
  field_simp

/-- The lower BG factor decreases on the positive half-line. -/
theorem fwMeanA_antitoneOn : AntitoneOn fwMeanA (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : 0 < a := ha
  have h1 : 1/b ≤ 1/a := one_div_le_one_div_of_le ha' hab
  have h2 : 2/b^2 ≤ 2/a^2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos ha' 2)
      (pow_le_pow_left₀ ha'.le hab 2)
  have h3 : 6/b^3 ≤ 6/a^3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos ha' 3)
      (pow_le_pow_left₀ ha'.le hab 3)
  dsimp [fwMeanA]
  linarith

/-- The upper BG factor decreases on the positive half-line. -/
theorem fwMeanB_antitoneOn : AntitoneOn fwMeanB (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : 0 < a := ha
  have h1 : 1/b ≤ 1/a := one_div_le_one_div_of_le ha' hab
  have h2 : 4/b^2 ≤ 4/a^2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos ha' 2)
      (pow_le_pow_left₀ ha'.le hab 2)
  dsimp [fwMeanB]
  linarith

/-- On a positive closed cell each scaled BG factor lies between its
values at the right and left endpoints. -/
theorem fw_mean_cell_bounds {a u b : ℝ} (ha : 0 < a)
    (hau : a ≤ u) (hub : u ≤ b) :
    fwMeanA b ≤ fwMeanA u ∧ fwMeanA u ≤ fwMeanA a ∧
      fwMeanB b ≤ fwMeanB u ∧ fwMeanB u ≤ fwMeanB a := by
  have hu : 0 < u := lt_of_lt_of_le ha hau
  have hb : 0 < b := lt_of_lt_of_le hu hub
  exact ⟨fwMeanA_antitoneOn hu hb hub, fwMeanA_antitoneOn ha hu hau,
    fwMeanB_antitoneOn hu hb hub, fwMeanB_antitoneOn ha hu hau⟩

end
end Sude
