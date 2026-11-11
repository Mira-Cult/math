import Sude.FWSubwheelDomination

/-! Computable 105-wheel unit enumeration. Finite facts are checked by the
Lean kernel; no radius, source recipe or growth claim is made. -/
namespace Sude
noncomputable section

/-- Unit residues in the positive interval 1..105. -/
def fwWheel105Residue (i : Fin 48) : ℕ := ![1,2,4,8,11,13,16,17,19,22,23,26,29,31,32,34,37,38,41,43,44,46,47,52,53,58,59,61,62,64,67,68,71,73,74,76,79,82,83,86,88,89,92,94,97,101,103,104] i

/-- Periodic enumeration in the same order as `fwWheelUnit 105`. -/
def fwWheel105Unit (i : ℕ) : ℕ :=
  fwWheel105Residue ⟨i % 48, Nat.mod_lt _ (by decide)⟩ + (i / 48) * 105

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Each listed number is a 105-unit and has exactly i preceding units. -/
theorem fw_wheel105_initial_certificate : ∀ i : Fin 48,
    Nat.Coprime 105 (fwWheel105Residue i) ∧
    Nat.count (fun a : ℕ => Nat.Coprime 105 a) (fwWheel105Residue i) = i.val := by
  decide +kernel

/-- The first period agrees with the general ordered enumeration. -/
theorem fw_wheel105_unit_first_period (i : Fin 48) :
    fwWheelUnit 105 i = fwWheel105Residue i := by
  obtain ⟨hunit, hcount⟩ := fw_wheel105_initial_certificate i
  have h := Nat.nth_count hunit
  simpa [fwWheelUnit, hcount] using h

/-- The explicit formula equals the general wheel enumeration at every index. -/
theorem fw_wheel105_unit_eq (i : ℕ) : fwWheelUnit 105 i = fwWheel105Unit i := by
  have hf : Nat.totient 105 = 48 := by decide +kernel
  have hp := fw_wheel_period_iterate (fwWheelUnit 105) 105 48
    (by intro k; simpa [hf] using fw_wheel_unit_period 105 (by decide) k)
    (i % 48) (i / 48)
  have hindex : i % 48 + i / 48 * 48 = i := by
    simpa [Nat.mul_comm] using Nat.mod_add_div i 48
  rw [hindex] at hp
  have hb := fw_wheel105_unit_first_period ⟨i % 48, Nat.mod_lt _ (by decide)⟩
  rw [hb] at hp
  simpa [fwWheel105Unit] using hp

/-- The exact cutoff has an explicit wheel-105 representation. -/
theorem fw_wheel105_cutoff_computable (T : ℕ) :
    fwWheelWindowCutoff (fwWheelUnit 105) 105 (Nat.totient 105) T
      (Nat.totient_pos.mpr (by decide)) =
    fwWheelWindowCutoff fwWheel105Unit 105 48 T (by decide) := by
  have hf : Nat.totient 105 = 48 := by decide +kernel
  have hu : fwWheelUnit 105 = fwWheel105Unit := funext fw_wheel105_unit_eq
  simp only [hu, hf]

/-- Minimum distances for the 48 wheel-105 remainders. -/
def fwWheel105Offset (i : Fin 48) : ℕ := ![1,3,4,6,8,10,13,15,16,18,21,24,25,28,30,31,34,36,39,42,43,45,47,49,51,54,57,58,60,63,65,67,70,72,73,76,78,80,83,85,87,90,91,93,94,98,100,105] i

/-- Computable exact cutoff of the wheel-105 period. -/
def fwWheel105Cutoff (T : ℕ) : ℕ :=
  T / 48 * 105 + fwWheel105Offset ⟨T % 48, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- All 48 finite minima are computed by the Lean kernel. -/
theorem fw_wheel105_minima : ∀ i : Fin 48,
    fwWheelWindowMin fwWheel105Unit 48 (i.val + 1) (by decide) = fwWheel105Offset i := by
  decide +kernel

/-- The closed expression equals the general exact cutoff for every T. -/
theorem fw_wheel105_cutoff_eq (T : ℕ) :
    fwWheelWindowCutoff (fwWheelUnit 105) 105 (Nat.totient 105) T
      (Nat.totient_pos.mpr (by decide)) = fwWheel105Cutoff T := by
  rw [fw_wheel105_cutoff_computable]
  unfold fwWheelWindowCutoff fwWheel105Cutoff
  rw [fw_wheel105_minima ⟨T % 48, Nat.mod_lt _ (by decide)⟩]

end
end Sude
