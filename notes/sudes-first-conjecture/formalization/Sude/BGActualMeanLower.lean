import Sude.FWActualPoolMean

/-! A stronger lower mean bound on the BG logarithm interval. The BMOR and
RS inputs, order threshold and finite X cap are explicit; no later BG/WC
controller statement is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- On the initial sixteenth-width cell, the FW scalar enclosure is above
487/1000. Its small margin is established by exact rational arithmetic. -/
theorem bg_mean_first_cell_gate :
    let a : ℝ := 24
    let b : ℝ := 385 / 16
    let c : ℝ := (281649 / 62500 : ℝ) / 65536
    let W : ℝ := 2^32
    0 < fwMeanA b - c ∧
      (487 / 1000 : ℝ) < (fwMeanA (2*b)/2 - 2*c - 4*b/W^2)/(fwMeanB a+c) := by
  norm_num [fwMeanA, fwMeanB]

/-- The shifted eighth-width cells cover the remainder of [24,29] and retain
the stronger lower bound. The last cell extends slightly beyond 29. -/
theorem bg_mean_shifted_cell_gates (i : ℕ) (hi : i < 40) :
    let a : ℝ := (385 + 2*(i : ℝ))/16
    let b : ℝ := (387 + 2*(i : ℝ))/16
    let c : ℝ := (281649 / 62500 : ℝ) / 65536
    let W : ℝ := 2^32
    0 < fwMeanA b - c ∧
      (487 / 1000 : ℝ) < (fwMeanA (2*b)/2 - 2*c - 4*b/W^2)/(fwMeanB a+c) := by
  have hbound : i ≤ 39 := by omega
  interval_cases i <;> norm_num [fwMeanA, fwMeanB]

/-- Select a certified cell for any logarithm in the BG range. -/
theorem bg_mean_cells_cover {u : ℝ} (hlo : 24 ≤ u) (hhi : u ≤ 29) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ u ∧ u ≤ b ∧
      (let c : ℝ := (281649 / 62500 : ℝ) / 65536
       let W : ℝ := 2^32
       0 < fwMeanA b - c ∧
         (487 / 1000 : ℝ) < (fwMeanA (2*b)/2 - 2*c - 4*b/W^2)/(fwMeanB a+c)) := by
  by_cases hfirst : u ≤ (385 / 16 : ℝ)
  · exact ⟨24, 385/16, by norm_num, hlo, hfirst, bg_mean_first_cell_gate⟩
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
    refine ⟨(385+2*(i : ℝ))/16, (387+2*(i : ℝ))/16, ?_, ?_, ?_, bg_mean_shifted_cell_gates i hi⟩
    · positivity
    · dsimp [z] at *; linarith
    · dsimp [z] at *; linarith

/-- The prescribed pool has normalized mean above 0.487 when the explicit
prime-counting inputs and finite BG log and maximum range hold. -/
theorem bg_actual_pool_normalized_mean_lower (bmor : BMORFinitePiFour) (lower : RSIndexLower)
    {n : ℕ} (hn : 19485 ≤ n)
    (hloglo : (24 : ℝ) ≤ Real.log (poolMaximum n : ℝ))
    (hloghi : Real.log (poolMaximum n : ℝ) ≤ 29)
    (hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ)) :
    (487 / 1000 : ℝ) < ((Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ)) /
      (poolMaximum n : ℝ) := by
  let u : ℝ := Real.log (poolMaximum n : ℝ)
  let c : ℝ := (281649 / 62500 : ℝ) / 65536
  let W : ℝ := 2^32
  let q : ℝ := u * (((n*n : ℕ) : ℝ) / (poolMaximum n : ℝ))
  let m : ℝ := ((Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ)) / (poolMaximum n : ℝ)
  obtain ⟨a,b,ha,hau,hub,hcert⟩ := bg_mean_cells_cover hloglo hloghi
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
  have hs := fw_mean_scaled_bounds bmor lower hn hlog hcap hub
  dsimp only at hs
  change 0 < q ∧ fwMeanA u-c ≤ q ∧ q ≤ fwMeanB u+c ∧
    (fwMeanA (2*u)/2-c-c-4*b/W^2)/q ≤ m ∧
    m ≤ (fwMeanB (2*u)/2+c+c+fwMeanB u/W)/q at hs
  have ht := fw_mean_cell_transport ha hau hub hW hs.1 hs.2.1 hs.2.2.1
    (le_refl c) (le_refl c) (le_refl (4*b/W^2)) (le_refl (fwMeanB u/W))
    hcert.1 hnumlo hnumhi hs.2.2.2.1 hs.2.2.2.2
  change (487 / 1000 : ℝ) < m
  linarith [hcert.2, ht.1]

/-- Unnormalized version for the actual odd-prime pool mean. -/
theorem bg_actual_pool_mean_lower (bmor : BMORFinitePiFour) (lower : RSIndexLower)
    {n : ℕ} (hn : 19485 ≤ n)
    (hloglo : (24 : ℝ) ≤ Real.log (poolMaximum n : ℝ))
    (hloghi : Real.log (poolMaximum n : ℝ) ≤ 29)
    (hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ)) :
    (487 / 1000 : ℝ) * (poolMaximum n : ℝ) <
      (Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ) := by
  have hX : 0 < (poolMaximum n : ℝ) := by exact_mod_cast (poolMaximum_prime n).pos
  exact (lt_div_iff₀ hX).mp (bg_actual_pool_normalized_mean_lower bmor lower hn hloglo hloghi hcap)

end
end Sude
