import Sude.FWExactWheelWindow
import Mathlib.Data.Nat.Nth

/-! Ordered unit enumeration for the exact wheel-window theorem. -/
namespace Sude
noncomputable section

/-- The nonnegative units of a positive wheel in increasing order. -/
def fwWheelUnit (W i : ℕ) : ℕ := Nat.nth (fun a => W.Coprime a) i

/-- There are infinitely many units: the progression `1 + kW`. -/
theorem fw_wheel_units_infinite (W : ℕ) (hW : 0 < W) :
    (Set.ofPred (fun a : ℕ => W.Coprime a)).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 1 + k * W)
  · intro x y h
    change 1 + x * W = 1 + y * W at h
    have hmul : x * W = y * W := by omega
    exact Nat.eq_of_mul_eq_mul_right hW hmul
  · intro k
    change W.Coprime (1 + k * W)
    exact (Nat.coprime_add_mul_right_right W 1 k).mpr (Nat.coprime_one_right W)

/-- Enumerated wheel units are strictly increasing. -/
theorem fw_wheel_unit_strictMono (W : ℕ) (hW : 0 < W) : StrictMono (fwWheelUnit W) :=
  Nat.nth_strictMono (fw_wheel_units_infinite W hW)

/-- The enumeration covers exactly the natural units, including zero when W=1. -/
theorem fw_wheel_unit_enum (W : ℕ) (hW : 0 < W) (a : ℕ) :
    Nat.Coprime a W ↔ ∃ i, fwWheelUnit W i = a := by
  constructor
  · intro ha
    exact ⟨Nat.count (fun x => W.Coprime x) a, Nat.nth_count ha.symm⟩
  · rintro ⟨i, rfl⟩
    exact (Nat.nth_mem_of_infinite (fw_wheel_units_infinite W hW) i).symm

/-- Each complete wheel period contains exactly phi(W) units, independent
of the starting position. -/
theorem fw_wheel_shifted_count (W a : ℕ) :
    Nat.count (fun k => W.Coprime (a + k)) W = Nat.totient W := by
  rw [Nat.count_eq_card_filter_range, ← Nat.filter_coprime_Ico_eq_totient W a]
  apply Finset.card_bij (fun k _ => a + k)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨by omega, by omega⟩, hk.2⟩
  · intro i hi j hj h
    omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx
    refine ⟨x - a, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · omega
      · have h : a + (x - a) = x := by omega
        simpa [h] using hx.2
    · omega

/-- The sorted unit enumeration advances by W after phi(W) terms. -/
theorem fw_wheel_unit_period (W : ℕ) (hW : 0 < W) (i : ℕ) :
    fwWheelUnit W (i + Nat.totient W) = fwWheelUnit W i + W := by
  let p : ℕ → Prop := fun a => W.Coprime a
  have hinf : (Set.ofPred p).Infinite := fw_wheel_units_infinite W hW
  have hunit : p (fwWheelUnit W i) := Nat.nth_mem_of_infinite hinf i
  have hshift : p (fwWheelUnit W i + W) := Nat.coprime_add_self_right.mpr hunit
  have hcount : Nat.count p (fwWheelUnit W i + W) = i + Nat.totient W := by
    change Nat.count p (Nat.nth p i + W) = _
    rw [Nat.count_add, Nat.count_nth_of_infinite hinf, fw_wheel_shifted_count]
  have h := Nat.nth_count hshift
  rw [hcount] at h
  exact h

/-- The source cutoff is positive for every positive wheel and every T. -/
theorem fw_wheel_cutoff_pos_of_pos (W T : ℕ) (hW : 0 < W) :
    0 < fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
      (Nat.totient_pos.mpr hW) :=
  fw_wheel_cutoff_pos (fwWheelUnit W) W (Nat.totient W) T
    (Nat.totient_pos.mpr hW) (fw_wheel_unit_strictMono W hW)

/-- An unconditional WW window bound for each positive wheel. -/
theorem fw_wheel_window_bound_of_pos (W T a : ℕ) (hW : 0 < W)
    (ha : Nat.Coprime a W) :
    ((Finset.Ico 1 (fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
      (Nat.totient_pos.mpr hW))).filter (fun j => Nat.Coprime (a + j) W)).card ≤ T := by
  exact fw_wheel_window_bound (fwWheelUnit W) W (Nat.totient W) T
    (Nat.totient_pos.mpr hW) (fw_wheel_unit_strictMono W hW)
    (fw_wheel_unit_period W hW) (fw_wheel_unit_enum W hW) a ha

end
end Sude
