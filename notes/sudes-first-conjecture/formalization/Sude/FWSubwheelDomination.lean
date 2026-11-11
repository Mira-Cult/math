import Sude.FWWheelEnumeration

/-! Exact WW cutoff monotonicity when one wheel divides another. This is a
purely combinatorial comparison; no finite cutoff values are assumed. -/
namespace Sude
noncomputable section

/-- Every exact cutoff is attained as a successor distance. -/
theorem fw_wheel_cutoff_attained (W T : ℕ) (hW : 0 < W) :
    ∃ i : ℕ,
      fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
          (Nat.totient_pos.mpr hW) =
        fwWheelUnit W (i + (T + 1)) - fwWheelUnit W i := by
  let f := Nat.totient W
  have hf : 0 < f := Nat.totient_pos.mpr hW
  let s := T % f + 1
  let q := T / f
  have hmem := Finset.min'_mem ((Finset.range f).image
    (fun i => fwWheelUnit W (i + s) - fwWheelUnit W i))
      (by simp [Nat.ne_of_gt hf])
  obtain ⟨i, hi, hmin⟩ := Finset.mem_image.mp hmem
  refine ⟨i, ?_⟩
  have hperiod := fw_wheel_period_iterate (fwWheelUnit W) W f
    (fw_wheel_unit_period W hW) (i + s) q
  have hindex : i + s + q * f = i + (T + 1) := by
    dsimp [s, q]
    have hdiv : T % f + T / f * f = T := by
      simpa [Nat.mul_comm] using Nat.mod_add_div T f
    omega
  rw [hindex] at hperiod
  have hle : fwWheelUnit W i ≤ fwWheelUnit W (i + s) :=
    (fw_wheel_unit_strictMono W hW).monotone (by omega)
  change q * W + fwWheelWindowMin (fwWheelUnit W) f s hf = _
  unfold fwWheelWindowMin
  rw [hmin.symm, hperiod]
  omega

/-- Removing wheel units by adjoining factors can only enlarge the sharp
integer WW window. Covers all positive wheels, including d=1. -/
theorem fw_subwheel_cutoff_le (d W T : ℕ) (hd : 0 < d) (hW : 0 < W)
    (hdiv : d ∣ W) :
    fwWheelWindowCutoff (fwWheelUnit d) d (Nat.totient d) T
        (Nat.totient_pos.mpr hd) ≤
      fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
        (Nat.totient_pos.mpr hW) := by
  classical
  let kd := fwWheelWindowCutoff (fwWheelUnit d) d (Nat.totient d) T
    (Nat.totient_pos.mpr hd)
  let kW := fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
    (Nat.totient_pos.mpr hW)
  obtain ⟨i, hi⟩ := fw_wheel_cutoff_attained W T hW
  let a := fwWheelUnit W i
  let u := fwWheelUnit W
  have hmono : StrictMono u := fw_wheel_unit_strictMono W hW
  have hunitW : ∀ j, Nat.Coprime (u j) W := by
    intro j
    exact (Nat.nth_mem_of_infinite (fw_wheel_units_infinite W hW) j).symm
  have hunitd : ∀ j, Nat.Coprime (u j) d := by
    intro j
    exact Nat.Coprime.of_dvd_right hdiv (hunitW j)
  have ha : Nat.Coprime a d := hunitd i
  have hupper := fw_wheel_window_bound_of_pos d T a hd ha
  change ((Finset.Ico 1 kd).filter (fun j => Nat.Coprime (a+j) d)).card ≤ T at hupper
  by_contra hnot
  have hk : kW < kd := by omega
  have hle : u i ≤ u (i + (T + 1)) := hmono.monotone (by omega)
  have hdistance : kW = u (i + (T + 1)) - u i := hi
  let window := (Finset.Ico 1 kd).filter (fun j => Nat.Coprime (a+j) d)
  have hcount : T + 1 ≤ window.card := by
    have hh : (Finset.range (T + 1)).card ≤ window.card := by
      apply Finset.card_le_card_of_injOn (fun r => u (i+r+1) - u i)
      · intro r hr
        have hrlt : r < T + 1 := Finset.mem_range.mp hr
        have hlt : u i < u (i+r+1) := hmono (by omega)
        have hle' : u (i+r+1) ≤ u (i+(T+1)) := hmono.monotone (by omega)
        change u (i+r+1) - u i ∈ window
        simp only [window, Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        have heq : a + (u (i+r+1) - u i) = u (i+r+1) := by
          change u i + (u (i+r+1) - u i) = u (i+r+1)
          omega
        rw [heq]
        exact hunitd _
      · intro r hr s hs heq
        change u (i+r+1) - u i = u (i+s+1) - u i at heq
        have hrle : u i ≤ u (i+r+1) := hmono.monotone (by omega)
        have hsle : u i ≤ u (i+s+1) := hmono.monotone (by omega)
        have hu : u (i+r+1) = u (i+s+1) := by omega
        have hind := hmono.injective hu
        omega
    simpa using hh
  change window.card ≤ T at hupper
  omega

end
end Sude
