import Sude.FWWheelEnumeration

/-! Universal lower bounds on exact wheel cutoffs. No finite wheel period is
computed here; only strict monotonicity and the totient bound are used. -/
namespace Sude
noncomputable section

/-- In any strictly increasing natural enumeration, the s-th successor is
at least s steps later. -/
theorem fw_wheel_window_min_ge_steps (u : ℕ → ℕ) (f s : ℕ)
    (hf : 0 < f) (hmono : StrictMono u) :
    s ≤ fwWheelWindowMin u f s hf := by
  unfold fwWheelWindowMin
  have hmem := Finset.min'_mem ((Finset.range f).image (fun i => u (i + s) - u i))
    (by simp [Nat.ne_of_gt hf])
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  have hstep := hmono.add_le_nat s i
  rw [Nat.add_comm s i] at hstep
  omega

/-- For every positive wheel, the exact WW window is at least T+1.
This also applies to W=1 and T=0. -/
theorem fw_wheel_cutoff_ge_succ (W T : ℕ) (hW : 0 < W) :
    T + 1 ≤ fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
      (Nat.totient_pos.mpr hW) := by
  let f := Nat.totient W
  have hf : 0 < f := Nat.totient_pos.mpr hW
  have htot : f ≤ W := Nat.totient_le W
  have hmin := fw_wheel_window_min_ge_steps (fwWheelUnit W) f (T % f + 1)
    hf (fw_wheel_unit_strictMono W hW)
  have hmul := Nat.mul_le_mul_left (T / f) htot
  have hdiv : T % f + T / f * f = T := by
    simpa [Nat.mul_comm] using Nat.mod_add_div T f
  change T + 1 ≤ (T / f) * W + fwWheelWindowMin (fwWheelUnit W) f (T % f + 1) hf
  omega

end
end Sude
