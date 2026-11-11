import Sude.BGThetaMeanGates
import Sude.OddCountScaledMean

/-! The BG lower mean bound from a supplied aggregate count estimate. The
    proposed theta-to-count derivation remains an explicit missing input. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Select a certified cell for any logarithm in the BG range. -/
theorem bg_theta_mean_cells_cover {u : ℝ} (hlo : 24 ≤ u) (hhi : u ≤ 29) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ u ∧ u ≤ b ∧
      (let c : ℝ := (1367 / 250 : ℝ) / 131072
       let W : ℝ := 2^32
       0 < fwMeanA b - c ∧
         (487 / 1000 : ℝ) < (fwMeanA (2*b)/2 - 2*c - 4*b/W^2)/(fwMeanB a+c)) := by
  by_cases hfirst : u ≤ (385 / 16 : ℝ)
  · exact ⟨24, 385/16, by norm_num, hlo, hfirst, bg_theta_mean_first_cell_gate⟩
  · have hu : (385 / 16 : ℝ) ≤ u := (lt_of_not_ge hfirst).le
    let z : ℝ := 8*u - 385/2
    have hz : 0 ≤ z := by dsimp [z]; linarith
    have hzupper : z < 40 := by dsimp [z]; linarith
    let i : ℕ := ⌊z⌋₊
    have hil : (i : ℝ) ≤ z := Nat.floor_le hz
    have hiu : z < (i : ℝ) + 1 := Nat.lt_floor_add_one z
    have hi : i < 40 := by
      have h : (i : ℝ) < 40 := lt_of_le_of_lt hil hzupper
      exact_mod_cast h
    refine ⟨(385+2*(i : ℝ))/16, (387+2*(i : ℝ))/16, ?_, ?_, ?_, bg_theta_mean_shifted_cell_gates i hi⟩
    · positivity
    · dsimp [z] at *; linarith
    · dsimp [z] at *; linarith

/-- The prescribed pool has normalized mean above 0.487 when the explicit
prime-counting inputs and finite BG log and maximum range hold. -/
theorem bg_actual_pool_normalized_mean_lower_of_aggregate
    {n : ℕ} (hn : 0 < n)
    (hloglo : (24 : ℝ) ≤ Real.log (poolMaximum n : ℝ))
    (hloghi : Real.log (poolMaximum n : ℝ) ≤ 29)
    (hcount : OddPrimeCountUniformBound (poolMaximum n : ℝ)
      ((1367 / 250 : ℝ) * (Real.sqrt (poolMaximum n : ℝ) /
        Real.log (poolMaximum n : ℝ)))) :
    (487 / 1000 : ℝ) < ((Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ)) /
      (poolMaximum n : ℝ) := by
  let u : ℝ := Real.log (poolMaximum n : ℝ)
  let c : ℝ := (1367 / 250 : ℝ) / 131072
  let W : ℝ := 2^32
  let q : ℝ := u * (((n*n : ℕ) : ℝ) / (poolMaximum n : ℝ))
  let m : ℝ := ((Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ)) / (poolMaximum n : ℝ)
  obtain ⟨a,b,ha,hau,hub,hcert⟩ := bg_theta_mean_cells_cover hloglo hloghi
  have hW : 0 < W := by dsimp [W]; positivity
  have hc : 0 < c := by dsimp [c]; norm_num
  dsimp only at hcert
  change 0 < fwMeanA b - c ∧
    (487 / 1000 : ℝ) < (fwMeanA (2*b)/2 - 2*c - 4*b/W^2)/(fwMeanB a+c) at hcert
  have hden : 0 < fwMeanB a + c := by
    have hB : 0 < fwMeanB a := by dsimp [fwMeanB]; positivity
    linarith
  have hnumlo : 0 ≤ fwMeanA (2*b)/2 - 2*c - 4*b/W^2 := by
    have ht := (lt_div_iff₀ hden).mp hcert.2
    have hp := mul_pos (by norm_num : (0 : ℝ) < 487 / 1000) hden
    linarith
  have hnumhi : 0 ≤ fwMeanB (2*a)/2 + 2*c + fwMeanB a/W := by
    have ha2 : 0 < 2*a := by positivity
    have hb2 : 0 < fwMeanB (2*a) := by dsimp [fwMeanB]; positivity
    have hb1 : 0 < fwMeanB a := by dsimp [fwMeanB]; positivity
    positivity
  have hlog : 22 ≤ Real.log (poolMaximum n : ℝ) := by linarith
  obtain ⟨hXbound, hsqrt⟩ := odd_count_bg_pool_scales hloglo
  have hs := odd_count_mean_scaled_bounds hn hlog hXbound
    (1367 / 250 : ℝ) 131072 (by norm_num) hsqrt hcount hub
  dsimp only at hs
  change 0 < q ∧ fwMeanA u-c ≤ q ∧ q ≤ fwMeanB u+c ∧
    (fwMeanA (2*u)/2-c-c-4*b/W^2)/q ≤ m ∧
    m ≤ (fwMeanB (2*u)/2+c+c+fwMeanB u/W)/q at hs
  have ht := fw_mean_cell_transport ha hau hub hW hs.1 hs.2.1 hs.2.2.1
    (le_refl c) (le_refl c) (le_refl (4*b/W^2)) (le_refl (fwMeanB u/W))
    hcert.1 hnumlo hnumhi hs.2.2.2.1 hs.2.2.2.2
  change (487 / 1000 : ℝ) < m
  linarith [hcert.2, ht.1]


end
end Sude
