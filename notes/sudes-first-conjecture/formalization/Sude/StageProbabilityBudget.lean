import Sude.PermutationStageMGF

/-! Exact logarithmic budget for the simultaneous weighted-stage allocation. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
local instance stageBudgetPermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- The strict-failure estimate, with the zero-proxy case kept explicit. -/
def zeroAwareTailBound (p : NNReal) (ε : ℝ) : ℝ :=
  if p = 0 then 0 else 2 * Real.exp (-ε ^ 2 / (2 * (p : ℝ)))

/-- If a proxy is at most one quarter of a common variance invoice, the
source logarithmic threshold gives failure probability at most `1/(2m)`. -/
theorem zeroAwareTailBound_log_budget (m : ℕ) (hm : 0 < m) (V : ℝ) (hV : 0 ≤ V)
    (p : NNReal) (hp : (p : ℝ) ≤ V / 4) :
    zeroAwareTailBound p (Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2)) ≤
      1 / (2 * (m : ℝ)) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hM : 1 < 4 * (m : ℝ) := by
    have hm1nat : 1 ≤ m := by omega
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm1nat
    linarith
  have hlog : 0 ≤ Real.log (4 * (m : ℝ)) := Real.log_nonneg (le_of_lt hM)
  have harg : 0 ≤ V * Real.log (4 * (m : ℝ)) / 2 := by positivity
  have hsq : (Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2)) ^ 2 =
      V * Real.log (4 * (m : ℝ)) / 2 := Real.sq_sqrt harg
  by_cases hp0 : p = 0
  · simp [zeroAwareTailBound, hp0, le_of_lt hmR]
  · have hpR : 0 < (p : ℝ) := by
      have hp' : 0 < p := pos_iff_ne_zero.mpr hp0
      exact_mod_cast hp'
    have hden : 0 < 2 * (p : ℝ) := by positivity
    have hmul : (2 * (p : ℝ)) * Real.log (4 * (m : ℝ)) ≤
        (V / 2) * Real.log (4 * (m : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hlog
      linarith [hp]
    have hratio : Real.log (4 * (m : ℝ)) ≤
        (Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2)) ^ 2 / (2 * (p : ℝ)) := by
      apply (le_div_iff₀ hden).2
      rw [hsq]
      nlinarith [hmul]
    have hexp : Real.exp (-(Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2)) ^ 2 / (2 * (p : ℝ))) ≤
        Real.exp (-Real.log (4 * (m : ℝ))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      exact neg_le_neg hratio
    have hlogexp : Real.exp (-Real.log (4 * (m : ℝ))) = (4 * (m : ℝ))⁻¹ := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
    rw [zeroAwareTailBound, if_neg hp0]
    calc
      _ ≤ 2 * (4 * (m : ℝ))⁻¹ := by rw [← hlogexp]; gcongr
      _ = 1 / (2 * (m : ℝ)) := by field_simp; ring

/-- The sum of zero-aware line-failure bounds is at most one half. -/
theorem zeroAwareTailBound_sum_log_budget (m : ℕ) (hm : 0 < m) (V : ℝ) (hV : 0 ≤ V)
    (p : Fin m → NNReal) (hp : ∀ l, (p l : ℝ) ≤ V / 4) :
    (∑ l, zeroAwareTailBound (p l) (Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2))) ≤ 1 / 2 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  calc
    _ ≤ ∑ _l : Fin m, (1 / (2 * (m : ℝ))) := by
      apply Finset.sum_le_sum
      intro l hl
      exact zeroAwareTailBound_log_budget m hm V hV (p l) (hp l)
    _ = 1 / 2 := by
      simp
      field_simp

/-- Source-form simultaneous allocation with a common variance invoice.
The remaining task at an application is to prove the line-proxy cap from
the actual physical slot incidences. -/
theorem stageLines_exists_of_proxy_cap {m r n : ℕ} (hm : 0 < m)
    (slots : Fin m → Fin r → Finset (Fin n)) (weights : Fin m → Fin r → Fin n → ℝ)
    (values : Fin r → Fin n → ℝ) (lo upper : Fin r → ℝ) (V : ℝ) (hV : 0 ≤ V)
    (hnonneg : ∀ l i j, j ∈ slots l i → 0 ≤ weights l i j)
    (hvalues : ∀ i a, values i a ∈ Set.Icc (lo i) (upper i))
    (hproxy : ∀ l, ((stageWeightedProxy (slots l) (weights l) lo upper : NNReal) : ℝ) ≤ V / 4) :
    ∃ ω : Fin r → Equiv.Perm (Fin n), ∀ l,
      |stageLineCentered slots weights values l ω| ≤
        Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2) := by
  let ε : ℝ := Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2)
  have hε : 0 ≤ ε := Real.sqrt_nonneg _
  have hb := zeroAwareTailBound_sum_log_budget m hm V hV
    (fun l => stageWeightedProxy (slots l) (weights l) lo upper) hproxy
  have hbudget : (∑ l, stageStrictFailureBound (slots l) (weights l) lo upper ε) < 1 := by
    have h : (∑ l, stageStrictFailureBound (slots l) (weights l) lo upper ε) ≤ 1 / 2 := by
      change (∑ l, zeroAwareTailBound (stageWeightedProxy (slots l) (weights l) lo upper) ε) ≤ 1 / 2
      exact hb
    linarith
  exact stageLines_simultaneous_exists_le slots weights values lo upper (fun _ => ε)
    hnonneg hvalues (fun _ => hε) hbudget

end
end Sude
