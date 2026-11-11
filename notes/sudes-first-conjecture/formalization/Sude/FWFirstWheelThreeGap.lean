import Sude.FWWindowCutoffLower
import Sude.FWAffineBaseCertificate

/-! Stronger exact-window lower bound using the factor 3 of the first
FW wheel. This uses no finite wheel-window enumeration. -/
namespace Sude
noncomputable section

/-- Three consecutive integers cannot all be units of 15015. -/
theorem fw_first_wheel_two_successor_gap (i : ℕ) :
    fwWheelUnit 15015 i + 3 ≤ fwWheelUnit 15015 (i + 2) := by
  let u := fwWheelUnit 15015
  have hmono := fw_wheel_unit_strictMono 15015 (by decide)
  have h1 : u i < u (i + 1) := hmono (by omega)
  have h2 : u (i + 1) < u (i + 2) := hmono (by omega)
  have hnot : ∀ k, ¬ 3 ∣ u k := by
    intro k
    have hunit : Nat.Coprime 3 (u k) :=
      (Nat.nth_mem_of_infinite (fw_wheel_units_infinite 15015 (by decide)) k).coprime_dvd_left (by decide)
    exact (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mp hunit
  have hm0 : u i % 3 ≠ 0 := by intro h; exact hnot i (Nat.dvd_of_mod_eq_zero h)
  have hm1 : u (i + 1) % 3 ≠ 0 := by intro h; exact hnot (i+1) (Nat.dvd_of_mod_eq_zero h)
  have hm2 : u (i + 2) % 3 ≠ 0 := by intro h; exact hnot (i+2) (Nat.dvd_of_mod_eq_zero h)
  change u i + 3 ≤ u (i + 2)
  omega

/-- Every s-th successor of a first-wheel unit is at least s+floor(s/2)
positions later. -/
theorem fw_first_wheel_successor_gap (i s : ℕ) :
    s + s / 2 ≤ fwWheelUnit 15015 (i + s) - fwWheelUnit 15015 i := by
  let u := fwWheelUnit 15015
  have hpairs : ∀ k : ℕ, u i + 3 * k ≤ u (i + 2 * k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := fw_first_wheel_two_successor_gap (i + 2 * k)
      change u (i + 2*k) + 3 ≤ u (i + 2*k + 2) at h
      have heq : i + 2 * (k + 1) = i + 2*k + 2 := by omega
      rw [heq]
      omega
  have hrem := (fw_wheel_unit_strictMono 15015 (by decide)).add_le_nat (s % 2) (i + 2 * (s / 2))
  have hs : 2 * (s / 2) + s % 2 = s := by omega
  have heq : i + 2 * (s / 2) + s % 2 = i + s := by omega
  have heq' : s % 2 + (i + 2 * (s / 2)) = i + s := by omega
  rw [heq'] at hrem
  have h := hpairs (s / 2)
  change s % 2 + u (i + 2 * (s / 2)) ≤ u (i + s) at hrem
  change s + s / 2 ≤ u (i + s) - u i
  omega

/-- The exact minimum over a whole wheel period satisfies the same bound. -/
theorem fw_first_wheel_window_min_gap (s : ℕ) :
    s + s / 2 ≤ fwWheelWindowMin (fwWheelUnit 15015) (Nat.totient 15015) s
      (Nat.totient_pos.mpr (by decide)) := by
  unfold fwWheelWindowMin
  have hmem := Finset.min'_mem ((Finset.range (Nat.totient 15015)).image
      (fun i => fwWheelUnit 15015 (i + s) - fwWheelUnit 15015 i)) (by simp)
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  rw [← hi]
  exact fw_first_wheel_successor_gap i s

set_option maxRecDepth 8192 in
/-- The exact first-wheel cutoff exceeds the trivial T+1 bound by half
its successor count, uniformly for every T. -/
theorem fw_first_wheel_cutoff_three_lower (T : ℕ) :
    T + 1 + (T + 1) / 2 ≤
      fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
        (Nat.totient_pos.mpr (by decide)) := by
  have hmin := fw_first_wheel_window_min_gap (T % Nat.totient 15015 + 1)
  have hdiv : T % Nat.totient 15015 + T / Nat.totient 15015 * Nat.totient 15015 = T := by
    simpa [Nat.mul_comm] using Nat.mod_add_div T (Nat.totient 15015)
  have hdiv' : T % Nat.totient 15015 + T / Nat.totient 15015 * 5760 = T := by
    simpa only [fw_base_wheel_totient] using hdiv
  have ha : ∀ q r z : ℕ, r + q * 5760 = T → r + 1 + (r + 1) / 2 ≤ z →
      T + 1 + (T + 1) / 2 ≤ q * 15015 + z := by
    intro q r z hq hz
    omega
  change T + 1 + (T + 1) / 2 ≤
    (T / Nat.totient 15015) * 15015 +
      fwWheelWindowMin (fwWheelUnit 15015) (Nat.totient 15015)
        (T % Nat.totient 15015 + 1) (Nat.totient_pos.mpr (by decide))
  exact ha _ _ _ hdiv' hmin

end
end Sude
