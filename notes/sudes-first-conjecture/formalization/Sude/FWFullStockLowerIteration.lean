import Sude.FWFullStockIteration

/-! A generic integer lower recurrence for a supplied full-stock schedule.
The numerical step and its relationship to the enhanced threshold are explicit;
this file neither computes a first-band radius nor proves crossing. -/
namespace Sude
noncomputable section

/-- Iterate a stage-indexed lower increment from the supplied global index. -/
def fwFullStockLowerIter (F : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, r => r
  | k + 1, j, r => fwFullStockLowerIter F k (j + 1) (r + F j r)

/-- Iterating over two blocks advances the global stage index by the exact
length of the first block. -/
theorem fw_full_stock_lower_iter_add (F : ℕ → ℕ → ℕ) (a b j r : ℕ) :
    fwFullStockLowerIter F (a + b) j r =
      fwFullStockLowerIter F b (j + a) (fwFullStockLowerIter F a j r) := by
  induction a generalizing j r with
  | zero => simp [fwFullStockLowerIter]
  | succ a ih =>
    simp only [Nat.succ_add, fwFullStockLowerIter]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (j + 1) (r + F j r)

/-- Monotone increment bounds give a monotone finite lower recurrence. -/
theorem fw_full_stock_lower_iter_mono (F : ℕ → ℕ → ℕ)
    (hmono : ∀ j, Monotone (F j)) (k j : ℕ) :
    Monotone (fwFullStockLowerIter F k j) := by
  induction k generalizing j with
  | zero => intro a b hab; simpa [fwFullStockLowerIter] using hab
  | succ k ih =>
    intro a b hab
    have hinc := hmono j hab
    have hnext : a + F j a ≤ b + F j b := Nat.add_le_add hab hinc
    exact ih (j + 1) hnext

/-- A supplied labeled schedule dominates any monotone lower recurrence,
provided each proposed increment is bounded by every selected gap satisfying
that stage's recorded enhanced threshold. The stage index is the global index
recorded in `FWFullStockSchedule`. -/
theorem fw_full_stock_schedule_lower_iter
    (F : ℕ → ℕ → ℕ) (i : Fin 8) (n : ℕ)
    (hmono : ∀ j, Monotone (F j))
    (hstep : ∀ j R gap : ℕ, j < 238 →
      fwFullStockEnhancedD i j R ≤ (gap : ℝ) → F j R ≤ gap)
    {j actual actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWFullStockSchedule i n j actual actualFinal stages) :
    ∀ r : ℕ, r ≤ actual → fwFullStockLowerIter F stages.length j r ≤ actualFinal := by
  induction sched with
  | nil j actual =>
    intro r hr
    simpa [fwFullStockLowerIter] using hr
  | cons j actual actualFinal stage tail hcap hbefore hshift hminimum hpositive heven
      henhanced hplus hupper hrest ih =>
    intro r hr
    have hbound := hstep j actual stage.gap hcap henhanced
    have hnext : r + F j r ≤ actual + stage.gap := by
      have hinc := hmono j hr
      omega
    simpa [fwFullStockLowerIter] using ih (r + F j r) hnext

/-- A localized version needs the step bound and monotonicity only from a
specified global index and radius floor. Every following radius remains above
that floor because the increments are natural numbers. -/
theorem fw_full_stock_schedule_lower_iter_of_bounds
    (F : ℕ → ℕ → ℕ) (i : Fin 8) (n jmin floor : ℕ)
    (hmono : ∀ j, jmin ≤ j → j < 238 → Monotone (F j))
    (hstep : ∀ j R gap : ℕ, jmin ≤ j → j < 238 → floor ≤ R →
      fwFullStockEnhancedD i j R ≤ (gap : ℝ) → F j R ≤ gap)
    {j actual actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWFullStockSchedule i n j actual actualFinal stages)
    (hj : jmin ≤ j) :
    ∀ r : ℕ, floor ≤ r → r ≤ actual →
      fwFullStockLowerIter F stages.length j r ≤ actualFinal := by
  induction sched with
  | nil j actual =>
    intro r _ hr
    simpa [fwFullStockLowerIter] using hr
  | cons j actual actualFinal stage tail hcap hbefore hshift hminimum hpositive heven
      henhanced hplus hupper hrest ih =>
    intro r hfloor hr
    have hactual : floor ≤ actual := le_trans hfloor hr
    have hbound := hstep j actual stage.gap hj hcap hactual henhanced
    have hnext : r + F j r ≤ actual + stage.gap := by
      have hinc := hmono j hj hcap hr
      omega
    have hfinal := ih (by omega) (r + F j r) (by omega) hnext
    simpa [fwFullStockLowerIter] using hfinal

end
end Sude
