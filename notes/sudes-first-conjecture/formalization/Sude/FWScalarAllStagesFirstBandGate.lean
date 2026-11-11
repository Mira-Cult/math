import Sude.FWScalarEndpointFirstBandGate

/-! Uniform scalar first-band gate for all P ≤ 238. This is a statement
about the scalar envelope only, not the FW checker or a physical line. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768

/-- The endpoint comparison extends the strict first-band scalar gate to
all natural stage counts up to 238. -/
theorem fw_scalar_all_stages_first_band_gate (n P : ℕ)
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hP : P ≤ 238) :
    let K : ℝ := (n / 450 : ℕ)
    let κ : ℝ := 19033 / 450
    let N := fwScalarEnvelopeN n K P
    let T := fwScalarEnvelopeT n K P
    0 < N ∧
      T / N < κ * (201 / 10000 : ℝ) ∧
      T / N < κ * (9992985347481480 / 497023611807928513 : ℝ) := by
  dsimp only
  have he := fw_scalar_endpoint_first_band_gate n hnlo hnhi
  dsimp only at he
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hK : (0 : ℝ) ≤ (n / 450 : ℕ) := Nat.cast_nonneg _
  have hPr : (P : ℝ) ≤ 238 := by exact_mod_cast hP
  have hm := fw_scalar_envelope_monotone_in_P (n : ℝ) ((n / 450 : ℕ) : ℝ) (P : ℝ)
    hn hK (Nat.cast_nonneg _) hPr he.1
  dsimp only at hm
  have hkpos : (0 : ℝ) < 19033 / 450 := by norm_num
  have hend : fwScalarEnvelopeT n ((n / 450 : ℕ) : ℝ) 238 /
      fwScalarEnvelopeN n ((n / 450 : ℕ) : ℝ) 238 <
      (19033 / 450 : ℝ) * (201 / 10000 : ℝ) := by
    have hh : fwScalarEnvelopeT n ((n / 450 : ℕ) : ℝ) 238 /
        fwScalarEnvelopeN n ((n / 450 : ℕ) : ℝ) 238 / (19033 / 450 : ℝ) <
        (201 / 10000 : ℝ) := by simpa only [div_div] using he.2.1
    have hh' := (div_lt_iff₀ hkpos).mp hh
    nlinarith
  have hfirst := lt_of_le_of_lt hm.2.2.2.2 hend
  refine ⟨hm.2.2.2.1, hfirst, ?_⟩
  exact lt_trans hfirst (mul_lt_mul_of_pos_left he.2.2 hkpos)

end
end Sude
