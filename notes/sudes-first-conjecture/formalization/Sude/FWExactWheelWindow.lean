import Sude.FWSeedTraceGrid

/-! A conditional, all-`T` form of the exact wheel window (WW1--WW2).
See `problems/prime-line-sums/manuscripts/cutoff2_exact_wheel_window.md`.
The ordered enumeration and its period are explicit hypotheses; constructing
that enumeration from a wheel and applying it to prime entries are separate. -/
namespace Sude
noncomputable section

/-- Minimum distance to the `s`th following unit over one enumeration period. -/
def fwWheelWindowMin (u : ℕ → ℕ) (f s : ℕ) (hf : 0 < f) : ℕ :=
  ((Finset.range f).image (fun i => u (i + s) - u i)).min' (by simp [Nat.ne_of_gt hf])

/-- Source cutoff, with quotient and remainder in the enumeration period. -/
def fwWheelWindowCutoff (u : ℕ → ℕ) (W f T : ℕ) (hf : 0 < f) : ℕ :=
  (T / f) * W + fwWheelWindowMin u f (T % f + 1) hf

/-- Iterating the period identity shifts the ordered enumeration exactly. -/
theorem fw_wheel_period_iterate (u : ℕ → ℕ) (W f : ℕ)
    (hperiod : ∀ i, u (i + f) = u i + W) (i q : ℕ) :
    u (i + q * f) = u i + q * W := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show i + (q + 1) * f = (i + q * f) + f by ring, hperiod, ih]
    simp only [Nat.succ_mul]
    omega

/-- A strictly increasing enumeration has a positive minimum distance to
any strictly later successor. -/
theorem fw_wheel_min_pos (u : ℕ → ℕ) (f s : ℕ) (hf : 0 < f)
    (hs : 0 < s) (hmono : StrictMono u) : 0 < fwWheelWindowMin u f s hf := by
  unfold fwWheelWindowMin
  have hmem := Finset.min'_mem ((Finset.range f).image (fun i => u (i + s) - u i))
    (by simp [Nat.ne_of_gt hf])
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  have hlt : u i < u (i + s) := hmono (by omega)
  omega

/-- Each source cutoff is positive, including the case `T = 0`. -/
theorem fw_wheel_cutoff_pos (u : ℕ → ℕ) (W f T : ℕ) (hf : 0 < f)
    (hmono : StrictMono u) : 0 < fwWheelWindowCutoff u W f T hf := by
  have h := fw_wheel_min_pos u f (T % f + 1) hf (by omega) hmono
  unfold fwWheelWindowCutoff
  omega

/-- The finite-period minimum bounds the `s`th successor distance at every
index, including indices outside the chosen period. -/
theorem fw_wheel_min_le_successor (u : ℕ → ℕ) (W f s : ℕ) (hf : 0 < f)
    (hperiod : ∀ i, u (i + f) = u i + W) (i : ℕ) :
    fwWheelWindowMin u f s hf ≤ u (i + s) - u i := by
  have hmin : fwWheelWindowMin u f s hf ≤ u (i % f + s) - u (i % f) := by
    unfold fwWheelWindowMin
    apply Finset.min'_le
    apply Finset.mem_image.mpr
    exact ⟨i % f, Finset.mem_range.mpr (Nat.mod_lt i hf), rfl⟩
  have hi : i % f + (i / f) * f = i := by
    simpa [Nat.mul_comm] using Nat.mod_add_div i f
  have h0 := fw_wheel_period_iterate u W f hperiod (i % f) (i / f)
  have hs := fw_wheel_period_iterate u W f hperiod (i % f + s) (i / f)
  have hi' : i % f + s + i / f * f = i + s := by omega
  rw [hi] at h0
  rw [hi'] at hs
  omega

/-- The cutoff lies no later than the `(T+1)`st subsequent unit in the
ordered enumeration. -/
theorem fw_wheel_cutoff_le_next (u : ℕ → ℕ) (W f T : ℕ) (hf : 0 < f)
    (hperiod : ∀ i, u (i + f) = u i + W) (hmono : StrictMono u) (i : ℕ) :
    fwWheelWindowCutoff u W f T hf ≤ u (i + T + 1) - u i := by
  have hmin := fw_wheel_min_le_successor u W f (T % f + 1) hf hperiod i
  have hperiod' := fw_wheel_period_iterate u W f hperiod (i + (T % f + 1)) (T / f)
  have heq : i + (T % f + 1) + T / f * f = i + T + 1 := by
    have h : T % f + T / f * f = T := by
      simpa [Nat.mul_comm] using Nat.mod_add_div T f
    omega
  rw [heq] at hperiod'
  have hle : u i ≤ u (i + (T % f + 1)) := hmono.monotone (by omega)
  unfold fwWheelWindowCutoff
  omega

/-- WW3 under a supplied ordered periodic enumeration of the wheel units:
for every unit start and every natural `T`, fewer than the cutoff admits at
most `T` later units. The equality assumption on `u` is explicit. -/
theorem fw_wheel_window_bound (u : ℕ → ℕ) (W f T : ℕ) (hf : 0 < f)
    (hmono : StrictMono u) (hperiod : ∀ i, u (i + f) = u i + W)
    (henum : ∀ a, Nat.Coprime a W ↔ ∃ i, u i = a)
    (a : ℕ) (ha : Nat.Coprime a W) :
    ((Finset.Ico 1 (fwWheelWindowCutoff u W f T hf)).filter
      (fun j => Nat.Coprime (a + j) W)).card ≤ T := by
  classical
  obtain ⟨i, rfl⟩ := (henum a).mp ha
  have hnext := fw_wheel_cutoff_le_next u W f T hf hperiod hmono i
  let gaps : Finset ℕ := (Finset.range T).image (fun r => u (i + r + 1) - u i)
  have hsub : (Finset.Ico 1 (fwWheelWindowCutoff u W f T hf)).filter
      (fun j => Nat.Coprime (u i + j) W) ⊆ gaps := by
    intro j hj
    obtain ⟨hjrange, hjunit⟩ := Finset.mem_filter.mp hj
    have hjbounds := Finset.mem_Ico.mp hjrange
    obtain ⟨k, hk⟩ := (henum (u i + j)).mp hjunit
    have hik : i < k := hmono.lt_iff_lt.mp (by omega)
    have hki : k < i + T + 1 := by
      apply hmono.lt_iff_lt.mp
      omega
    apply Finset.mem_image.mpr
    refine ⟨k - (i + 1), Finset.mem_range.mpr (by omega), ?_⟩
    have hindex : i + (k - (i + 1)) + 1 = k := by omega
    rw [hindex, hk]
    omega
  calc
    _ ≤ gaps.card := Finset.card_le_card hsub
    _ ≤ T := by
      simpa [gaps] using (Finset.card_image_le (s := Finset.range T)
        (f := fun r => u (i + r + 1) - u i))

/-- The degenerate wheel `W=1` is covered by the same theorem for every T. -/
theorem fw_wheel_one_window_bound (T a : ℕ) :
    ((Finset.Ico 1 (fwWheelWindowCutoff id 1 1 T (by omega))).filter
      (fun j => Nat.Coprime (a + j) 1)).card ≤ T := by
  apply fw_wheel_window_bound id 1 1 T (by omega)
  · exact strictMono_id
  · intro i
    rfl
  · intro x
    constructor
    · intro _
      exact ⟨x, rfl⟩
    · intro _
      exact Nat.coprime_one_right x
  · exact Nat.coprime_one_right a


end
end Sude
