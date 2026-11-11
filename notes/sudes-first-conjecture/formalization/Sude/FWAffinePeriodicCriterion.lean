import Sude.FWAffineWheelExtension

/-! A finite-period prefix criterion for the two-sided AW discrepancy.
The criterion is independent of any numerical wheel computation. -/
namespace Sude
noncomputable section

/-- Number of wheel units at positions 1 through n. -/
def fwPeriodPrefix (W n : ℕ) : ℕ := Nat.count (fun x => Nat.Coprime W (x + 1)) n

theorem fw_period_prefix_add_period (W n : ℕ) :
    fwPeriodPrefix W (n + W) = fwPeriodPrefix W n + Nat.totient W := by
  unfold fwPeriodPrefix
  rw [Nat.count_add]
  congr 1
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fw_wheel_shifted_count W (n + 1)

theorem fw_period_prefix_div (W n : ℕ) :
    fwPeriodPrefix W n = (n / W) * Nat.totient W + fwPeriodPrefix W (n % W) := by
  have h : ∀ q r : ℕ, fwPeriodPrefix W (q * W + r) =
      q * Nat.totient W + fwPeriodPrefix W r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      have heq : (q + 1) * W + r = (q * W + r) + W := by ring
      rw [heq, fw_period_prefix_add_period, ih]
      ring
  have hn := h (n / W) (n % W)
  rw [Nat.mul_comm (n / W) W, Nat.div_add_mod] at hn
  exact hn

theorem fw_period_prefix_interval (W a K : ℕ) :
    fwPeriodPrefix W (a + K) = fwPeriodPrefix W a + (fwIntervalUnits W a K).card := by
  unfold fwPeriodPrefix
  rw [Nat.count_add]
  congr 1
  rw [Nat.count_eq_card_filter_range]
  rw [fw_interval_units_eq_window_card]
  apply Finset.card_bij (fun k _ => k + 1)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, by simpa [Nat.coprime_comm, Nat.add_assoc] using hk.2⟩
  · intro i _ j _ h; omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj
    refine ⟨j-1, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have heq : j - 1 + 1 = j := by omega
    simpa [Nat.coprime_comm, Nat.add_assoc, heq] using hj.2

/-- Signed scaled discrepancy of the first n positions. -/
def fwPeriodPrefixError (W n : ℕ) : ℤ :=
  (W : ℤ) * (fwPeriodPrefix W n : ℤ) - (Nat.totient W : ℤ) * n

theorem fw_period_prefix_error_mod (W n : ℕ) :
    fwPeriodPrefixError W n = fwPeriodPrefixError W (n % W) := by
  have hp := fw_period_prefix_div W n
  have hn := Nat.div_add_mod n W
  have hnZ : (W : ℤ) * (n / W : ℕ) + (n % W : ℕ) = n := by exact_mod_cast hn
  unfold fwPeriodPrefixError
  rw [hp]
  push_cast
  nlinarith

/-- It suffices to check the scaled prefix discrepancy at the `W` residues;
periodicity and interval subtraction then give the full AW1 hypothesis. -/
theorem fw_affine_interval_discrepancy_of_prefix_bounds
    (W : ℕ) (hW : 0 < W) (lo hi : ℤ)
    (hbounds : ∀ r < W, lo ≤ fwPeriodPrefixError W r ∧ fwPeriodPrefixError W r ≤ hi) :
    FWAffineIntervalDiscrepancy W ((Nat.totient W : ℝ) / W) (((hi - lo : ℤ) : ℝ) / W) := by
  intro a K
  have ha := hbounds (a % W) (Nat.mod_lt a hW)
  have hb := hbounds ((a + K) % W) (Nat.mod_lt _ hW)
  rw [← fw_period_prefix_error_mod] at ha hb
  have hc := fw_period_prefix_interval W a K
  have hcZ : (fwPeriodPrefix W (a + K) : ℤ) =
      (fwPeriodPrefix W a : ℤ) + (fwIntervalUnits W a K).card := by exact_mod_cast hc
  unfold fwPeriodPrefixError at ha hb
  have hscaled : (lo - hi) ≤
      (W : ℤ) * ((fwIntervalUnits W a K).card : ℤ) - (Nat.totient W : ℤ) * K ∧
      (W : ℤ) * ((fwIntervalUnits W a K).card : ℤ) - (Nat.totient W : ℤ) * K ≤ hi - lo := by
    push_cast at hb
    constructor <;> nlinarith
  have hscaledR : ((lo - hi : ℤ) : ℝ) ≤
      (W : ℝ) * ((fwIntervalUnits W a K).card : ℝ) - (Nat.totient W : ℝ) * K ∧
      (W : ℝ) * ((fwIntervalUnits W a K).card : ℝ) - (Nat.totient W : ℝ) * K ≤ ((hi - lo : ℤ) : ℝ) := by
    exact_mod_cast hscaled
  have hWp : (0 : ℝ) < W := by exact_mod_cast hW
  constructor
  · rw [div_mul_eq_mul_div, ← sub_div]
    apply (div_le_iff₀ hWp).2
    push_cast at hscaledR ⊢
    nlinarith [hscaledR.1]
  · rw [div_mul_eq_mul_div, ← add_div]
    apply (le_div_iff₀ hWp).2
    push_cast at hscaledR ⊢
    nlinarith [hscaledR.2]

end
end Sude
