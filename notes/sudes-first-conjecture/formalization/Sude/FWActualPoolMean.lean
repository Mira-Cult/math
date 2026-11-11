import Sude.FWMeanCellCover
import Sude.FWMeanCellTransport
import Sude.FWMeanScaledBounds

/-! The finite FW mean interval from explicit BMOR/RS inputs and a supplied
logarithm range. The proof uses exact rational cells. -/
namespace Sude
noncomputable section

/-- The actual normalized mean lies inside FW's required interval whenever
the explicit source hypotheses and the FW logarithmic range hold. -/
theorem fw_actual_pool_normalized_mean (bmor : BMORFinitePiFour) (lower : RSIndexLower)
    {n : ℕ} (hn : 19485 ≤ n)
    (hloglo : (181 / 8 : ℝ) ≤ Real.log (poolMaximum n : ℝ))
    (hloghi : Real.log (poolMaximum n : ℝ) ≤ 29)
    (hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ)) :
    (243 / 500 : ℝ) ≤ ((Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ)) /
      (poolMaximum n : ℝ) ∧
    ((Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ)) / (poolMaximum n : ℝ) ≤
      (123 / 250 : ℝ) := by
  let u : ℝ := Real.log (poolMaximum n : ℝ)
  let c : ℝ := (281649 / 62500 : ℝ) / 65536
  let W : ℝ := 2^32
  let q : ℝ := u * (((n*n : ℕ) : ℝ) / (poolMaximum n : ℝ))
  let m : ℝ := ((Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ)) / (poolMaximum n : ℝ)
  obtain ⟨i, hi, hai, hbi⟩ := fw_mean_cells_cover hloglo hloghi
  let a : ℝ := (181 + (i : ℝ))/8
  let b : ℝ := (182 + (i : ℝ))/8
  have ha : 0 < a := by dsimp [a]; positivity
  have hau : a ≤ u := hai
  have hub : u ≤ b := hbi
  have hW : 0 < W := by dsimp [W]; positivity
  have hc : 0 < c := by dsimp [c]; norm_num
  have hcert := fw_mean_rational_cells i hi
  dsimp only at hcert
  change 0 < fwMeanA b - c ∧
    (243 / 500 : ℝ) < (fwMeanA (2*b)/2 - 2*c - 4*b/W^2)/(fwMeanB a+c) ∧
    (fwMeanB (2*a)/2 + 2*c + fwMeanB a/W)/(fwMeanA b-c) < (123 / 250 : ℝ) at hcert
  have hden : 0 < fwMeanB a + c := by
    have hB : 0 < fwMeanB a := by dsimp [fwMeanB]; positivity
    linarith
  have hnumlo : 0 ≤ fwMeanA (2*b)/2 - 2*c - 4*b/W^2 := by
    have ht := (lt_div_iff₀ hden).mp hcert.2.1
    have hp := mul_pos (by norm_num : (0 : ℝ) < 243 / 500) hden
    linarith
  have hnumhi : 0 ≤ fwMeanB (2*a)/2 + 2*c + fwMeanB a/W := by
    have ha2 : 0 < 2*a := by positivity
    have hb2 : 0 < fwMeanB (2*a) := by dsimp [fwMeanB]; positivity
    have hb1 : 0 < fwMeanB a := by dsimp [fwMeanB]; positivity
    positivity
  have hlog : 22 ≤ Real.log (poolMaximum n : ℝ) := by linarith
  have hs := fw_mean_scaled_bounds bmor lower hn hlog hcap hub
  dsimp only at hs
  change 0 < q ∧ fwMeanA u-c ≤ q ∧ q ≤ fwMeanB u+c ∧
    (fwMeanA (2*u)/2-c-c-4*b/W^2)/q ≤ m ∧
    m ≤ (fwMeanB (2*u)/2+c+c+fwMeanB u/W)/q at hs
  have ht := fw_mean_cell_transport ha hau hub hW hs.1 hs.2.1 hs.2.2.1
    (le_refl c) (le_refl c) (le_refl (4*b/W^2)) (le_refl (fwMeanB u/W))
    hcert.1 hnumlo hnumhi hs.2.2.2.1 hs.2.2.2.2
  change (243 / 500 : ℝ) ≤ m ∧ m ≤ (123 / 250 : ℝ)
  constructor <;> linarith [hcert.2.1, hcert.2.2, ht.1, ht.2]

/-- The same result in the unnormalized form required by FW matched bins. -/
theorem fw_actual_pool_mean_bounds (bmor : BMORFinitePiFour) (lower : RSIndexLower)
    {n : ℕ} (hn : 19485 ≤ n)
    (hloglo : (181 / 8 : ℝ) ≤ Real.log (poolMaximum n : ℝ))
    (hloghi : Real.log (poolMaximum n : ℝ) ≤ 29)
    (hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ)) :
    (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤
      (Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ) ∧
    (Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ) ≤
      (123 / 250 : ℝ) * (poolMaximum n : ℝ) := by
  have hX : 0 < (poolMaximum n : ℝ) := by
    exact_mod_cast (poolMaximum_prime n).pos
  have h := fw_actual_pool_normalized_mean bmor lower hn hloglo hloghi hcap
  exact ⟨(le_div_iff₀ hX).mp h.1, (div_le_iff₀ hX).mp h.2⟩

end
end Sude
