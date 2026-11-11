import Sude.FWScalarEnvelopeMonotonicity
/-! Exact scalar endpoint gate for the FW first-band order range.
No physical full-line or existence conclusion is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- Five exact quotient cases certify a positive endpoint denominator and
both strict rational comparisons across the first-band order range. -/
theorem fw_scalar_endpoint_first_band_gate (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    let K : ℝ := (n / 450 : ℕ)
    let κ : ℝ := 19033 / 450
    0 < fwScalarEnvelopeN n K 238 ∧
    fwScalarEnvelopeT n K 238 / (fwScalarEnvelopeN n K 238 * κ) < (201 / 10000 : ℝ) ∧
    (201 / 10000 : ℝ) < 9992985347481480 / 497023611807928513 := by
  dsimp only
  have hG : 0 < fwScalarEnvelopeN n (n / 450 : ℕ) 238 ∧
      fwScalarEnvelopeT n (n / 450 : ℕ) 238 < (1275211 / 1500000 : ℝ) * fwScalarEnvelopeN n (n / 450 : ℕ) 238 := by
    by_cases h21 : n ≤ 21248
    · have hcases : n / 450 = 43 ∨ n / 450 = 44 ∨ n / 450 = 45 ∨ n / 450 = 46 ∨ n / 450 = 47 := by omega
      rcases hcases with hc | hc | hc | hc | hc
      · have hnat : 19485 ≤ n := by omega
        have hreal : (19485 : ℝ) ≤ n := by exact_mod_cast hnat
        have hk : ((n / 450 : ℕ) : ℝ) = 43 := by exact_mod_cast hc
        rw [hk]
        have hsquare := mul_nonneg (show (0 : ℝ) ≤ n by positivity) (show (0 : ℝ) ≤ (n : ℝ) - 19485 by linarith)
        constructor <;> dsimp [fwScalarEnvelopeN, fwScalarEnvelopeT, fwScalarEnvelopeA, fwScalarEnvelopeB, fwScalarEnvelopeR] <;>
          norm_num <;> nlinarith [hsquare]
      · have hnat : 19800 ≤ n := by omega
        have hreal : (19800 : ℝ) ≤ n := by exact_mod_cast hnat
        have hk : ((n / 450 : ℕ) : ℝ) = 44 := by exact_mod_cast hc
        rw [hk]
        have hsquare := mul_nonneg (show (0 : ℝ) ≤ n by positivity) (show (0 : ℝ) ≤ (n : ℝ) - 19800 by linarith)
        constructor <;> dsimp [fwScalarEnvelopeN, fwScalarEnvelopeT, fwScalarEnvelopeA, fwScalarEnvelopeB, fwScalarEnvelopeR] <;>
          norm_num <;> nlinarith [hsquare]
      · have hnat : 20250 ≤ n := by omega
        have hreal : (20250 : ℝ) ≤ n := by exact_mod_cast hnat
        have hk : ((n / 450 : ℕ) : ℝ) = 45 := by exact_mod_cast hc
        rw [hk]
        have hsquare := mul_nonneg (show (0 : ℝ) ≤ n by positivity) (show (0 : ℝ) ≤ (n : ℝ) - 20250 by linarith)
        constructor <;> dsimp [fwScalarEnvelopeN, fwScalarEnvelopeT, fwScalarEnvelopeA, fwScalarEnvelopeB, fwScalarEnvelopeR] <;>
          norm_num <;> nlinarith [hsquare]
      · have hnat : 20700 ≤ n := by omega
        have hreal : (20700 : ℝ) ≤ n := by exact_mod_cast hnat
        have hk : ((n / 450 : ℕ) : ℝ) = 46 := by exact_mod_cast hc
        rw [hk]
        have hsquare := mul_nonneg (show (0 : ℝ) ≤ n by positivity) (show (0 : ℝ) ≤ (n : ℝ) - 20700 by linarith)
        constructor <;> dsimp [fwScalarEnvelopeN, fwScalarEnvelopeT, fwScalarEnvelopeA, fwScalarEnvelopeB, fwScalarEnvelopeR] <;>
          norm_num <;> nlinarith [hsquare]
      · have hnat : 21150 ≤ n := by omega
        have hreal : (21150 : ℝ) ≤ n := by exact_mod_cast hnat
        have hk : ((n / 450 : ℕ) : ℝ) = 47 := by exact_mod_cast hc
        rw [hk]
        have hsquare := mul_nonneg (show (0 : ℝ) ≤ n by positivity) (show (0 : ℝ) ≤ (n : ℝ) - 21150 by linarith)
        constructor <;> dsimp [fwScalarEnvelopeN, fwScalarEnvelopeT, fwScalarEnvelopeA, fwScalarEnvelopeB, fwScalarEnvelopeR] <;>
          norm_num <;> nlinarith [hsquare]
    · have _ := hnhi
      have hnat : 21249 ≤ n := by omega
      have hreal : (21249 : ℝ) ≤ n := by exact_mod_cast hnat
      have hdiv : ((n / 450 : ℕ) : ℝ) * 450 ≤ n := by exact_mod_cast Nat.div_mul_le_self n 450
      have hK0 : (0 : ℝ) ≤ ((n / 450 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hKn := mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) - 450 * ((n / 450 : ℕ) : ℝ) by linarith)
        (show (0 : ℝ) ≤ (n : ℝ) + 8 by linarith)
      have hKn2 := mul_nonneg (show (0 : ℝ) ≤ n by positivity)
        (show (0 : ℝ) ≤ (n : ℝ) - 450 * ((n / 450 : ℕ) : ℝ) by linarith)
      have hsquare := mul_nonneg (show (0 : ℝ) ≤ n by positivity) (show (0 : ℝ) ≤ (n : ℝ) - 21249 by linarith)
      constructor <;> dsimp [fwScalarEnvelopeN, fwScalarEnvelopeT, fwScalarEnvelopeA, fwScalarEnvelopeB, fwScalarEnvelopeR] <;>
        norm_num <;> nlinarith [hKn, hKn2, hsquare]
  refine ⟨hG.1, ?_, by norm_num⟩
  have hkpos : (0 : ℝ) < 19033 / 450 := by norm_num
  apply (div_lt_iff₀ (mul_pos hG.1 hkpos)).2
  nlinarith [hG.2]

end
end Sude
