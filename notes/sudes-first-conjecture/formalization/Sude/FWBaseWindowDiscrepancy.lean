import Sude.FWAffineBaseCertificate

/-! Lower bound for the exact base-wheel window using the checked finite
interval discrepancy. This does not enumerate candidate windows or claim
any growth trace. -/
namespace Sude
noncomputable section

/-- For the base wheel, the interval from one enumerated unit to its s-th
successor contains exactly s units, with the left endpoint excluded. -/
theorem fw_base_wheel_successor_interval_count (i s : ℕ) :
    (fwIntervalUnits 15015 (fwWheelUnit 15015 i)
      (fwWheelUnit 15015 (i + s) - fwWheelUnit 15015 i)).card = s := by
  let p : ℕ → Prop := fun x => Nat.Coprime 15015 x
  have hinf : (Set.ofPred p).Infinite := fw_wheel_units_infinite 15015 (by decide)
  have hmono := fw_wheel_unit_strictMono 15015 (by decide)
  have hle : fwWheelUnit 15015 i ≤ fwWheelUnit 15015 (i + s) := hmono.monotone (by omega)
  have hprefix : ∀ j, fwPeriodPrefix 15015 (fwWheelUnit 15015 j) = j + 1 := by
    intro j
    have hcount : Nat.count p (fwWheelUnit 15015 j + 1) = j + 1 := by
      rw [Nat.count_succ]
      change Nat.count p (Nat.nth p j) + (if p (Nat.nth p j) then 1 else 0) = j + 1
      rw [Nat.count_nth_of_infinite hinf]
      simp [Nat.nth_mem_of_infinite hinf j]
    have hshift := Nat.count_add p 1 (fwWheelUnit 15015 j)
    have hzero : Nat.count p 1 = 0 := by decide
    rw [hzero, Nat.zero_add] at hshift
    have heq : Nat.count (fun k => p (1 + k)) (fwWheelUnit 15015 j) =
        fwPeriodPrefix 15015 (fwWheelUnit 15015 j) := by
      simp [fwPeriodPrefix, p, Nat.add_comm]
    rw [heq] at hshift
    have harg : 1 + fwWheelUnit 15015 j = fwWheelUnit 15015 j + 1 := by omega
    rw [harg, hcount] at hshift
    exact hshift.symm
  have hinterval := fw_period_prefix_interval 15015 (fwWheelUnit 15015 i)
    (fwWheelUnit 15015 (i + s) - fwWheelUnit 15015 i)
  rw [Nat.add_sub_of_le hle, hprefix (i+s), hprefix i] at hinterval
  omega

/-- The exact cutoff is attained as the distance from an enumerated wheel
unit to its (T+1)-st successor. -/
theorem fw_base_wheel_cutoff_attained (T : ℕ) :
    ∃ i : ℕ,
      fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
          (Nat.totient_pos.mpr (by decide)) =
        fwWheelUnit 15015 (i + (T + 1)) - fwWheelUnit 15015 i := by
  let f := Nat.totient 15015
  have hf : 0 < f := Nat.totient_pos.mpr (by decide)
  let s := T % f + 1
  let q := T / f
  have hmem := Finset.min'_mem ((Finset.range f).image
    (fun i => fwWheelUnit 15015 (i + s) - fwWheelUnit 15015 i))
      (by simp [Nat.ne_of_gt hf])
  obtain ⟨i, hi, hmin⟩ := Finset.mem_image.mp hmem
  refine ⟨i, ?_⟩
  have hperiod := fw_wheel_period_iterate (fwWheelUnit 15015) 15015 f
    (fw_wheel_unit_period 15015 (by decide)) (i + s) q
  have hindex : i + s + q * f = i + (T + 1) := by
    dsimp [s, q]
    have hdiv : T % f + T / f * f = T := by
      simpa [Nat.mul_comm] using Nat.mod_add_div T f
    omega
  rw [hindex] at hperiod
  have hle : fwWheelUnit 15015 i ≤ fwWheelUnit 15015 (i + s) :=
    (fw_wheel_unit_strictMono 15015 (by decide)).monotone (by omega)
  change q * 15015 + fwWheelWindowMin (fwWheelUnit 15015) f s hf = _
  unfold fwWheelWindowMin
  rw [hmin.symm, hperiod]
  omega

/-- Checked base discrepancy turns into a lower bound on every exact WW
window, uniformly for every natural T. -/
theorem fw_base_wheel_cutoff_discrepancy (T : ℕ) :
    1001 * (T + 1) ≤
      384 * fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
        (Nat.totient_pos.mpr (by decide)) + 6718 := by
  obtain ⟨i, hi⟩ := fw_base_wheel_cutoff_attained T
  let a := fwWheelUnit 15015 i
  let d := fwWheelUnit 15015 (i + (T + 1)) - a
  have hc := fw_base_wheel_successor_interval_count i (T + 1)
  change (fwIntervalUnits 15015 a d).card = T + 1 at hc
  have hb := (fw_base_wheel_interval_discrepancy a d).2
  rw [hc] at hb
  have hnat : (1001 * (T + 1) : ℕ) ≤ (384 * d + 6718 : ℕ) := by
    have : ((1001 * (T + 1) : ℕ) : ℝ) ≤ ((384 * d + 6718 : ℕ) : ℝ) := by
      push_cast
      norm_num at hb ⊢
      linarith
    exact_mod_cast this
  simpa [d, a, ← hi] using hnat

end
end Sude
