import Sude.BinomialEntropy

/-! The binomial mode needed for the source's lower entropy estimate. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- Unnormalised binomial mass for parameter `k/m`. -/
def binomialModeTerm (m k i : ℕ) : ℝ :=
  (m.choose i : ℝ) * (k : ℝ) ^ i * ((m - k : ℕ) : ℝ) ^ (m - i)

/-- Exact adjacent-term relation, with no division by a potentially zero
binomial coefficient. -/
theorem binomialModeTerm_step {m k i : ℕ} (hi : i < m) :
    ((i + 1 : ℕ) : ℝ) * ((m - k : ℕ) : ℝ) * binomialModeTerm m k (i + 1) =
      ((m - i : ℕ) : ℝ) * (k : ℝ) * binomialModeTerm m k i := by
  have hchoose : ((m.choose (i + 1) : ℕ) : ℝ) * ((i : ℝ) + 1) =
      ((m.choose i : ℕ) : ℝ) * (((m - (i + 1) : ℕ) : ℝ) + 1) := by
    have h : ((m.choose (i + 1) : ℕ) : ℝ) * ((i : ℝ) + 1) =
        ((m.choose i : ℕ) : ℝ) * ((m - i : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_succ_right_eq m i
    have hs : ((m - i : ℕ) : ℝ) = ((m - (i + 1) : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show m - i = m - (i + 1) + 1 by omega)
    rw [hs] at h
    exact h
  have hsub : m - i = (m - (i + 1)) + 1 := by omega
  unfold binomialModeTerm
  rw [hsub, pow_succ, pow_succ]
  push_cast
  calc
    _ = (((m.choose (i + 1) : ℕ) : ℝ) * ((i : ℝ) + 1)) *
      ((k : ℝ)^i * ((m - k : ℕ) : ℝ)^(m - (i + 1)) * k * ((m - k : ℕ) : ℝ)) := by ring
    _ = (((m.choose i : ℕ) : ℝ) * (((m - (i + 1) : ℕ) : ℝ) + 1)) *
      ((k : ℝ)^i * ((m - k : ℕ) : ℝ)^(m - (i + 1)) * k * ((m - k : ℕ) : ℝ)) := by rw [hchoose]
    _ = _ := by ring

/-- Before the mode, adjacent unnormalised masses are nondecreasing. -/
theorem binomialModeTerm_step_up {m k i : ℕ} (hk0 : 0 < k) (hkm : k < m) (hi : i < k) :
    binomialModeTerm m k i ≤ binomialModeTerm m k (i + 1) := by
  have him : i < m := by omega
  have hfac : ((i + 1 : ℕ) : ℝ) * ((m - k : ℕ) : ℝ) ≤
      ((m - i : ℕ) : ℝ) * (k : ℝ) := by
    have hn : (i + 1) * (m - k) ≤ (m - i) * k := by
      have hmk := Nat.sub_add_cancel (by omega : k ≤ m)
      have hmi := Nat.sub_add_cancel (by omega : i ≤ m)
      nlinarith
    exact_mod_cast hn
  have hpos : 0 < ((i + 1 : ℕ) : ℝ) * ((m - k : ℕ) : ℝ) := by
    have hsub : 0 < m - k := Nat.sub_pos_of_lt hkm
    positivity
  have hnonneg : 0 ≤ binomialModeTerm m k i := by unfold binomialModeTerm; positivity
  have h := mul_le_mul_of_nonneg_right hfac hnonneg
  rw [← binomialModeTerm_step him] at h
  exact le_of_mul_le_mul_left h hpos

/-- At and after the mode, adjacent masses are nonincreasing. -/
theorem binomialModeTerm_step_down {m k i : ℕ} (hk0 : 0 < k) (hkm : k < m)
    (hi : k ≤ i) (him : i < m) :
    binomialModeTerm m k (i + 1) ≤ binomialModeTerm m k i := by
  have hfac : ((m - i : ℕ) : ℝ) * (k : ℝ) ≤
      ((i + 1 : ℕ) : ℝ) * ((m - k : ℕ) : ℝ) := by
    have hn : (m - i) * k ≤ (i + 1) * (m - k) := by
      have hmk := Nat.sub_add_cancel (by omega : k ≤ m)
      have hmi := Nat.sub_add_cancel (by omega : i ≤ m)
      nlinarith
    exact_mod_cast hn
  have hpos : 0 < ((i + 1 : ℕ) : ℝ) * ((m - k : ℕ) : ℝ) := by
    have hsub : 0 < m - k := Nat.sub_pos_of_lt hkm
    positivity
  have hnonneg : 0 ≤ binomialModeTerm m k i := by unfold binomialModeTerm; positivity
  have h := mul_le_mul_of_nonneg_right hfac hnonneg
  rw [← binomialModeTerm_step him] at h
  exact le_of_mul_le_mul_left h hpos

/-- The unnormalised binomial mass with parameter `k/m` is maximised at `k`. -/
theorem binomialModeTerm_le_mode {m k i : ℕ} (hk0 : 0 < k) (hkm : k < m) (hi : i ≤ m) :
    binomialModeTerm m k i ≤ binomialModeTerm m k k := by
  have hup : MonotoneOn (binomialModeTerm m k) (Set.Icc 0 k) := by
    apply monotoneOn_of_le_succ Set.ordConnected_Icc
    intro j _ hj hjs
    have hlt : j < k := by
      have := hjs.2
      change j + 1 ≤ k at this
      omega
    exact binomialModeTerm_step_up hk0 hkm hlt
  have hdown : AntitoneOn (binomialModeTerm m k) (Set.Icc k m) := by
    apply antitoneOn_of_succ_le Set.ordConnected_Icc
    intro j _ hj hjs
    have hlt : j < m := by
      have := hjs.2
      change j + 1 ≤ m at this
      omega
    exact binomialModeTerm_step_down hk0 hkm hj.1 hlt
  by_cases hik : i ≤ k
  · exact hup ⟨Nat.zero_le _, hik⟩ ⟨Nat.zero_le _, le_rfl⟩ hik
  · exact hdown ⟨le_rfl, le_of_lt hkm⟩ ⟨by omega, hi⟩ (by omega)

/-- The unnormalised mass at the mode accounts for at least one of the
`m+1` terms of the exact binomial expansion. -/
theorem binomialModeTerm_mode_lower {m k : ℕ} (hk0 : 0 < k) (hkm : k < m) :
    (m : ℝ)^m ≤ (m + 1 : ℕ) * binomialModeTerm m k k := by
  have hsum := Finset.sum_le_card_nsmul (Finset.range (m + 1))
    (binomialModeTerm m k) (binomialModeTerm m k k) (by
      intro i hi
      exact binomialModeTerm_le_mode hk0 hkm (by simpa using Finset.mem_range.mp hi))
  have hsumid : (∑ i ∈ Finset.range (m + 1), binomialModeTerm m k i) = (m : ℝ)^m := by
    unfold binomialModeTerm
    have hcast : ((m - k : ℕ) : ℝ) + k = m := by
      exact_mod_cast Nat.sub_add_cancel (le_of_lt hkm)
    have h := add_pow (k : ℝ) ((m - k : ℕ) : ℝ) m
    have hadd : (k : ℝ) + ((m - k : ℕ) : ℝ) = m := by linarith
    rw [hadd] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsumid] at hsum
  simpa using hsum

/-- The exponential entropy factor is the reciprocal of the normalized
binomial mass at the mode. -/
theorem binomial_entropy_exp_eq_inv_mass {m k : ℕ} (hk0 : 0 < k) (hkm : k < m) :
    Real.exp ((m : ℝ) * Real.binEntropy ((k : ℝ) / m)) =
      (((k : ℝ) / m) ^ k * (1 - (k : ℝ) / m) ^ (m - k))⁻¹ := by
  let p : ℝ := (k : ℝ) / m
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hk : (0 : ℝ) < k := by exact_mod_cast hk0
  have hkm' : (k : ℝ) < m := by exact_mod_cast hkm
  have hp0 : 0 < p := div_pos hk hm
  have hp1 : p < 1 := (div_lt_one hm).2 hkm'
  have hr : 0 < p ^ k * (1 - p) ^ (m - k) :=
    mul_pos (pow_pos hp0 _) (pow_pos (by linarith) _)
  have hlog : (m : ℝ) * Real.binEntropy p =
      -Real.log (p ^ k * (1 - p) ^ (m - k)) := by
    rw [Real.binEntropy, Real.log_inv, Real.log_inv, Real.log_mul (ne_of_gt (pow_pos hp0 _))
      (ne_of_gt (pow_pos (by linarith : 0 < 1 - p) _)), Real.log_pow, Real.log_pow]
    have hmk : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by exact Nat.cast_sub (by omega : k ≤ m)
    rw [hmk]
    dsimp [p]
    field_simp
    ring
  rw [hlog, Real.exp_neg, Real.exp_log hr]

/-- Source G2: the binomial coefficient is at least the entropy exponential
up to the exact `m+1` factor, for every interior index. -/
theorem binomial_exp_entropy_le_succ_mul_choose {m k : ℕ} (hk0 : 0 < k) (hkm : k < m) :
    Real.exp ((m : ℝ) * Real.binEntropy ((k : ℝ) / m)) ≤
      ((m + 1 : ℕ) : ℝ) * (m.choose k : ℝ) := by
  let p : ℝ := (k : ℝ) / m
  let r : ℝ := p ^ k * (1 - p) ^ (m - k)
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hk : (0 : ℝ) < k := by exact_mod_cast hk0
  have hkm' : (k : ℝ) < m := by exact_mod_cast hkm
  have hp0 : 0 < p := div_pos hk hm
  have hp1 : p < 1 := (div_lt_one hm).2 hkm'
  have hr : 0 < r := mul_pos (pow_pos hp0 _) (pow_pos (by linarith) _)
  have hmp : 0 < (m : ℝ)^m := pow_pos hm _
  have hsub : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := Nat.cast_sub (by omega)
  have hpcomp : 1 - p = ((m - k : ℕ) : ℝ) / m := by
    dsimp [p]
    rw [hsub]
    field_simp
  have hpower : (m : ℝ)^k * (m : ℝ)^(m-k) = (m : ℝ)^m := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : k ≤ m)]
  have hnorm : (m : ℝ)^m * r =
      (k : ℝ)^k * ((m - k : ℕ) : ℝ)^(m-k) := by
    dsimp [r, p]
    rw [show 1 - (k : ℝ) / m = ((m - k : ℕ) : ℝ) / m by exact hpcomp]
    rw [div_pow, div_pow, ← mul_div_mul_comm, hpower]
    field_simp
  have hmode := binomialModeTerm_mode_lower hk0 hkm
  have hmul : (m : ℝ)^m * 1 ≤
      (m : ℝ)^m * (((m + 1 : ℕ) : ℝ) * (m.choose k : ℝ) * r) := by
    rw [show (m : ℝ)^m * (((m + 1 : ℕ) : ℝ) * (m.choose k : ℝ) * r) =
      ((m + 1 : ℕ) : ℝ) * (m.choose k : ℝ) * ((m : ℝ)^m * r) by ring, hnorm]
    simpa [binomialModeTerm, mul_assoc, mul_left_comm, mul_comm] using hmode
  have hnormalized : 1 ≤ ((m + 1 : ℕ) : ℝ) * (m.choose k : ℝ) * r :=
    le_of_mul_le_mul_left hmul hmp
  rw [binomial_entropy_exp_eq_inv_mass hk0 hkm]
  change r⁻¹ ≤ _
  rw [← one_div]
  exact (div_le_iff₀ hr).2 hnormalized

/-- Source G2 with both endpoint cases included. -/
theorem binomial_exp_entropy_le_succ_mul_choose_all {m k : ℕ} (hk : k ≤ m) :
    Real.exp ((m : ℝ) * Real.binEntropy ((k : ℝ) / m)) ≤
      ((m + 1 : ℕ) : ℝ) * (m.choose k : ℝ) := by
  by_cases hk0 : k = 0
  · subst k
    simp
  by_cases hkm : k = m
  · subst k
    have hm : (m : ℝ) ≠ 0 := by exact_mod_cast hk0
    simp [hm]
  exact binomial_exp_entropy_le_succ_mul_choose (Nat.pos_of_ne_zero hk0) (lt_of_le_of_ne hk hkm)

end
end Sude
