import Sude.BTGrowingIteration

/-! Exact algebra for the BT shifted-radius phase. -/
namespace Sude
noncomputable section

/-- BT6's identity, with every denominator explicitly nonzero. -/
theorem bt_shifted_width_identity (ζ η g M Mf R r X : ℝ)
    (hη : η ≠ 0) (hMf : Mf ≠ 0) (hr : r ≠ 0) (hX : X ≠ 0) :
    ζ * g * (η * M * R / (r * X) - 1 / 2) =
      ζ * η * g * M * (R - r * X / (2 * η * Mf)) / (r * X) +
        ζ * g / 2 * (M / Mf - 1) := by
  field_simp
  ring

/-- With stock above the paid terminal floor, the second term of BT6 is
nonnegative; all signs and denominators are explicit. -/
theorem bt_shifted_width_lower (ζ η g M Mf R r X : ℝ)
    (hζ : 0 ≤ ζ) (hη : 0 < η) (hg : 0 ≤ g) (hMf : 0 < Mf)
    (hM : Mf ≤ M) (hr : 0 < r) (hX : 0 < X) :
    ζ * η * g * M * (R - r * X / (2 * η * Mf)) / (r * X) ≤
      ζ * g * (η * M * R / (r * X) - 1 / 2) := by
  rw [bt_shifted_width_identity ζ η g M Mf R r X hη.ne' hMf.ne' hr.ne' hX.ne']
  have hratio : 0 ≤ M / Mf - 1 := by
    apply sub_nonneg.mpr
    exact (one_le_div hMf).2 hM
  have hterm : 0 ≤ ζ * g / 2 * (M / Mf - 1) := by positivity
  linarith

/-- BT8: selecting a gap at least the BT width multiplies the shifted
radius by the stated factor. This is purely algebraic and assumes no
controller-specific estimate or phase cap. -/
theorem bt_shifted_radius_growth (ζ η g M Mf R r X h : ℝ)
    (hζ : 0 ≤ ζ) (hη : 0 < η) (hg : 0 ≤ g) (hMf : 0 < Mf)
    (hM : Mf ≤ M) (hr : 0 < r) (hX : 0 < X)
    (hwidth : ζ * g * (η * M * R / (r * X) - 1 / 2) ≤ h) :
    (1 + ζ * η * g * M / (r * X)) * (R - r * X / (2 * η * Mf)) ≤
      R + h - r * X / (2 * η * Mf) := by
  have hlower := bt_shifted_width_lower ζ η g M Mf R r X hζ hη hg hMf hM hr hX
  have hmul : ζ * η * g * M * (R - r * X / (2 * η * Mf)) / (r * X) =
      (ζ * η * g * M / (r * X)) * (R - r * X / (2 * η * Mf)) := by ring
  rw [hmul] at hlower
  nlinarith

/-- BT7 pays the exponential phase-entry threshold. The shifted-radius
lower bound holds for any later stock at least the terminal floor. -/
theorem bt_phase_entry (ζ η g M Mf R r X ell : ℝ)
    (hζ : 0 < ζ) (hη : 0 < η) (hg : 0 < g) (hMf : 0 < Mf)
    (hM : Mf ≤ M) (hr : 0 < r) (hX : 0 < X)
    (hstart : r * X * Real.exp ell / (ζ * η * Mf) ≤ R - r * X / (2 * η * Mf)) :
    Real.exp ell ≤ (ζ * g * (η * M * R / (r * X) - 1 / 2)) / g := by
  let S := R - r * X / (2 * η * Mf)
  have hden : 0 < ζ * η * Mf := by positivity
  have hs : 0 ≤ S := by
    have hp : 0 ≤ r * X * Real.exp ell / (ζ * η * Mf) := by positivity
    exact hp.trans hstart
  have hpaid : r * X * Real.exp ell ≤ (ζ * η * Mf) * S := by
    simpa [S, mul_comm] using (div_le_iff₀ hden).mp hstart
  have hcompare : (ζ * η * Mf) * S ≤ (ζ * η * M) * S := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by positivity)) hs
  have hbound : r * X * Real.exp ell ≤ ζ * η * M * S := hpaid.trans hcompare
  have hrx : 0 < r * X := by positivity
  have hsmall : Real.exp ell ≤ ζ * η * M * S / (r * X) := by
    apply (le_div_iff₀ hrx).2
    nlinarith
  have hwidth := bt_shifted_width_lower ζ η g M Mf R r X hζ.le hη hg.le hMf hM hr hX
  have hwidth' : ζ * η * M * S / (r * X) ≤
      (ζ * g * (η * M * R / (r * X) - 1 / 2)) / g := by
    apply (le_div_iff₀ hg).2
    have heq : (ζ * η * M * S / (r * X)) * g =
        ζ * η * g * M * S / (r * X) := by ring
    rw [heq]
    exact hwidth
  exact hsmall.trans hwidth'

/-- A stage whose chosen gap is at most the current grid radius has at
most the source's factor-two overshoot. -/
theorem bt_stage_overshoot (R h : ℕ) (hh : h ≤ R) : R + h ≤ 2 * R := by omega

/-- The logarithmic lower bound used when summing the phase growth rates. -/
theorem bt_log_growth_lower (t : ℝ) (ht : 0 ≤ t) :
    t / (1 + t) ≤ Real.log (1 + t) := by
  have hlog := Real.le_log_one_add_of_nonneg ht
  have ha : 0 < 1 + t := by positivity
  have hb : 0 < t + 2 := by positivity
  have hfrac : t / (1 + t) ≤ 2 * t / (t + 2) := by
    apply (div_le_div_iff₀ ha hb).2
    nlinarith [sq_nonneg t]
  exact hfrac.trans hlog

/-- Summing the one-stage growth inequalities gives a certified lower bound
on the logarithm of the total phase growth. Sampling or numerical evaluation
is not involved. -/
theorem bt_log_phase_growth (S t : ℕ → ℝ) (N : ℕ) (hS : 0 < S 0)
    (ht : ∀ k < N, 0 ≤ t k)
    (hstep : ∀ k < N, (1 + t k) * S k ≤ S (k + 1)) :
    (∑ k ∈ Finset.range N, t k / (1 + t k)) ≤ Real.log (S N / S 0) := by
  have hpos : ∀ k ≤ N, 0 < S k := by
    intro k hk
    induction k with
    | zero => exact hS
    | succ k ih =>
      have hkN : k < N := by omega
      have hprev := ih (by omega)
      have hfactor : 0 < 1 + t k := by have := ht k hkN; positivity
      exact lt_of_lt_of_le (mul_pos hfactor hprev) (hstep k hkN)
  have hsum : ∀ k ≤ N, Real.log (S 0) + (∑ i ∈ Finset.range k, t i / (1 + t i)) ≤
      Real.log (S k) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hkN : k < N := by omega
      have hprev := ih (by omega)
      have hp : 0 < S k := hpos k (by omega)
      have hfactor : 0 < 1 + t k := by have := ht k hkN; positivity
      have hnext : 0 < S (k + 1) := hpos (k + 1) (by omega)
      have hlog := Real.log_le_log (mul_pos hfactor hp) (hstep k hkN)
      rw [Real.log_mul hfactor.ne' hp.ne'] at hlog
      have hbound := bt_log_growth_lower (t k) (ht k hkN)
      rw [Finset.sum_range_succ]
      linarith
  have hresult := hsum N le_rfl
  rw [Real.log_div (hpos N le_rfl).ne' hS.ne']
  linarith

/-- The uniform-denominator form used in BT9 before evaluating the stock
sum and controller-specific rational bounds. -/
theorem bt_log_phase_growth_uniform (S t : ℕ → ℝ) (N : ℕ) (tmax : ℝ) (hS : 0 < S 0)
    (ht : ∀ k < N, 0 ≤ t k) (hmax : 0 ≤ tmax)
    (htmax : ∀ k < N, t k ≤ tmax)
    (hstep : ∀ k < N, (1 + t k) * S k ≤ S (k + 1)) :
    (∑ k ∈ Finset.range N, t k) / (1 + tmax) ≤ Real.log (S N / S 0) := by
  have hsum : (∑ k ∈ Finset.range N, t k / (1 + tmax)) ≤
      ∑ k ∈ Finset.range N, t k / (1 + t k) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    have htk := ht k hkN
    have hle := htmax k hkN
    have ha : 0 < 1 + tmax := by positivity
    have hb : 0 < 1 + t k := by positivity
    apply (div_le_div_iff₀ ha hb).2
    nlinarith
  simp only [div_eq_mul_inv, ← Finset.sum_mul] at hsum ⊢
  exact hsum.trans (bt_log_phase_growth S t N hS ht hstep)

/-- Exact stock sum for `M_j = M_a - 2Qj`, including the empty phase. -/
theorem bt_linear_stock_sum (Ma Q : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range J, (Ma - 2 * Q * (j : ℝ))) =
      (J : ℝ) * Ma - Q * (J : ℝ) * ((J : ℝ) - 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- BT9's logarithmic growth lower bound for an exact linearly depleted
stock. `a` is the source coefficient `ζηg/(rX)`. -/
theorem bt_linear_phase_bound (S : ℕ → ℝ) (J : ℕ) (a Ma Q : ℝ)
    (hS : 0 < S 0) (ha : 0 ≤ a) (hMa : 0 ≤ Ma) (hQ : 0 ≤ Q)
    (hstock : ∀ j < J, 0 ≤ Ma - 2 * Q * (j : ℝ))
    (hstep : ∀ j < J, (1 + a * (Ma - 2 * Q * (j : ℝ))) * S j ≤ S (j + 1)) :
    a * ((J : ℝ) * Ma - Q * (J : ℝ) * ((J : ℝ) - 1)) / (1 + a * Ma) ≤
      Real.log (S J / S 0) := by
  let t : ℕ → ℝ := fun j => a * (Ma - 2 * Q * (j : ℝ))
  have ht : ∀ j < J, 0 ≤ t j := by
    intro j hj
    exact mul_nonneg ha (hstock j hj)
  have htmax : ∀ j < J, t j ≤ a * Ma := by
    intro j hj
    apply mul_le_mul_of_nonneg_left _ ha
    have hp : 0 ≤ 2 * Q * (j : ℝ) := by positivity
    linarith
  have h := bt_log_phase_growth_uniform S t J (a * Ma) hS ht (mul_nonneg ha hMa)
    htmax hstep
  have hsum : (∑ j ∈ Finset.range J, t j) =
      a * ((J : ℝ) * Ma - Q * (J : ℝ) * ((J : ℝ) - 1)) := by
    simp only [t, ← Finset.mul_sum, bt_linear_stock_sum]
  rw [hsum] at h
  exact h

/-- A certified logarithmic growth budget reaches a positive phase target.
This separates the abstract phase argument from numerical enclosures. -/
theorem bt_phase_target_of_log_budget (S0 SJ target budget : ℝ)
    (hS0 : 0 < S0) (hSJ : 0 < SJ) (htarget : 0 < target)
    (hbudget : Real.log (target / S0) ≤ budget)
    (hgrowth : budget ≤ Real.log (SJ / S0)) : target ≤ SJ := by
  have hlog := hbudget.trans hgrowth
  have hratio := (Real.log_le_log_iff (div_pos htarget hS0) (div_pos hSJ hS0)).mp hlog
  exact (div_le_div_iff_of_pos_right hS0).mp hratio

/-- A paid BT9 budget forces the phase target by the end of the allotted
stages, assuming all displayed one-stage growth and stock inequalities. -/
theorem bt_linear_phase_reaches_target (S : ℕ → ℝ) (J : ℕ) (a Ma Q target : ℝ)
    (hS : 0 < S 0) (ha : 0 ≤ a) (hMa : 0 ≤ Ma) (hQ : 0 ≤ Q) (htarget : 0 < target)
    (hstock : ∀ j < J, 0 ≤ Ma - 2 * Q * (j : ℝ))
    (hstep : ∀ j < J, (1 + a * (Ma - 2 * Q * (j : ℝ))) * S j ≤ S (j + 1))
    (hbudget : Real.log (target / S 0) ≤
      a * ((J : ℝ) * Ma - Q * (J : ℝ) * ((J : ℝ) - 1)) / (1 + a * Ma)) :
    target ≤ S J := by
  have hpos : ∀ j ≤ J, 0 < S j := by
    intro j hj
    induction j with
    | zero => exact hS
    | succ j ih =>
      have hjJ : j < J := by omega
      have hprev := ih (by omega)
      have hfactor : 0 < 1 + a * (Ma - 2 * Q * (j : ℝ)) := by
        have hm := mul_nonneg ha (hstock j hjJ)
        linarith
      exact lt_of_lt_of_le (mul_pos hfactor hprev) (hstep j hjJ)
  exact bt_phase_target_of_log_budget (S 0) (S J) target _ hS (hpos J le_rfl) htarget hbudget
    (bt_linear_phase_bound S J a Ma Q hS ha hMa hQ hstock hstep)

end
end Sude
