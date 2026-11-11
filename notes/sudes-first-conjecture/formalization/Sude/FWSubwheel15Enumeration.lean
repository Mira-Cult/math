import Sude.FWSubwheelDomination

/-! Computable periodic enumeration of the 15-wheel, with kernel-checked
initial values and proof of equivalence to the general ordered enumeration.
No source mixed-recipe or growth claim is made. -/
namespace Sude
noncomputable section

/-- Unit residues in the positive interval 1..15. -/
def fwWheel15Residue (i : Fin 8) : ℕ := ![1,2,4,7,8,11,13,14] i

/-- Computable periodic enumeration, in the same order as `fwWheelUnit 15`. -/
def fwWheel15Unit (i : ℕ) : ℕ :=
  fwWheel15Residue ⟨i % 8, Nat.mod_lt _ (by decide)⟩ + (i / 8) * 15

/-- The initial eight values are certified by exact finite counts. -/
theorem fw_wheel15_unit_first_period (i : Fin 8) :
    fwWheelUnit 15 i = fwWheel15Residue i := by
  have h0 : fwWheelUnit 15 0 = 1 := by
    have h := Nat.nth_count (show Nat.Coprime 15 1 by decide)
    have hc : Nat.count (fun a : ℕ => Nat.Coprime 15 a) 1 = 0 := by decide +kernel
    simpa [fwWheelUnit, hc] using h
  have h1 : fwWheelUnit 15 1 = 2 := by
    have h := Nat.nth_count (show Nat.Coprime 15 2 by decide)
    have hc : Nat.count (fun a : ℕ => Nat.Coprime 15 a) 2 = 1 := by decide +kernel
    simpa [fwWheelUnit, hc] using h
  have h2 : fwWheelUnit 15 2 = 4 := by
    have h := Nat.nth_count (show Nat.Coprime 15 4 by decide)
    have hc : Nat.count (fun a : ℕ => Nat.Coprime 15 a) 4 = 2 := by decide +kernel
    simpa [fwWheelUnit, hc] using h
  have h3 : fwWheelUnit 15 3 = 7 := by
    have h := Nat.nth_count (show Nat.Coprime 15 7 by decide)
    have hc : Nat.count (fun a : ℕ => Nat.Coprime 15 a) 7 = 3 := by decide +kernel
    simpa [fwWheelUnit, hc] using h
  have h4 : fwWheelUnit 15 4 = 8 := by
    have h := Nat.nth_count (show Nat.Coprime 15 8 by decide)
    have hc : Nat.count (fun a : ℕ => Nat.Coprime 15 a) 8 = 4 := by decide +kernel
    simpa [fwWheelUnit, hc] using h
  have h5 : fwWheelUnit 15 5 = 11 := by
    have h := Nat.nth_count (show Nat.Coprime 15 11 by decide)
    have hc : Nat.count (fun a : ℕ => Nat.Coprime 15 a) 11 = 5 := by decide +kernel
    simpa [fwWheelUnit, hc] using h
  have h6 : fwWheelUnit 15 6 = 13 := by
    have h := Nat.nth_count (show Nat.Coprime 15 13 by decide)
    have hc : Nat.count (fun a : ℕ => Nat.Coprime 15 a) 13 = 6 := by decide +kernel
    simpa [fwWheelUnit, hc] using h
  have h7 : fwWheelUnit 15 7 = 14 := by
    have h := Nat.nth_count (show Nat.Coprime 15 14 by decide)
    have hc : Nat.count (fun a : ℕ => Nat.Coprime 15 a) 14 = 7 := by decide +kernel
    simpa [fwWheelUnit, hc] using h
  fin_cases i <;> norm_num [fwWheel15Residue] <;> assumption

/-- The explicit formula equals the general wheel enumeration at every index. -/
theorem fw_wheel15_unit_eq (i : ℕ) : fwWheelUnit 15 i = fwWheel15Unit i := by
  have hf : Nat.totient 15 = 8 := by decide +kernel
  have hp := fw_wheel_period_iterate (fwWheelUnit 15) 15 8
    (by intro k; simpa [hf] using fw_wheel_unit_period 15 (by decide) k)
    (i % 8) (i / 8)
  have hindex : i % 8 + i / 8 * 8 = i := by
    simpa [Nat.mul_comm] using Nat.mod_add_div i 8
  rw [hindex] at hp
  have hb := fw_wheel15_unit_first_period ⟨i % 8, Nat.mod_lt _ (by decide)⟩
  rw [hb] at hp
  simpa [fwWheel15Unit] using hp

/-- The exact cutoff admits an explicit, decidable wheel-15 representation. -/
theorem fw_wheel15_cutoff_computable (T : ℕ) :
    fwWheelWindowCutoff (fwWheelUnit 15) 15 (Nat.totient 15) T
      (Nat.totient_pos.mpr (by decide)) =
    fwWheelWindowCutoff fwWheel15Unit 15 8 T (by decide) := by
  have hf : Nat.totient 15 = 8 := by decide +kernel
  have hu : fwWheelUnit 15 = fwWheel15Unit := funext fw_wheel15_unit_eq
  simp only [hu, hf]

/-- The minimum distances for the eight possible wheel-15 remainders. -/
def fwWheel15Offset (i : Fin 8) : ℕ := ![1,3,4,6,8,10,12,15] i

/-- Closed natural-number expression for the exact wheel-15 cutoff. -/
def fwWheel15Cutoff (T : ℕ) : ℕ :=
  T / 8 * 15 + fwWheel15Offset ⟨T % 8, Nat.mod_lt _ (by decide)⟩

/-- All eight finite minima are computed by the Lean kernel. -/
theorem fw_wheel15_minima : ∀ i : Fin 8,
    fwWheelWindowMin fwWheel15Unit 8 (i.val + 1) (by decide) = fwWheel15Offset i := by
  decide +kernel

/-- The closed cutoff expression equals the general exact window for every T. -/
theorem fw_wheel15_cutoff_eq (T : ℕ) :
    fwWheelWindowCutoff (fwWheelUnit 15) 15 (Nat.totient 15) T
      (Nat.totient_pos.mpr (by decide)) = fwWheel15Cutoff T := by
  rw [fw_wheel15_cutoff_computable]
  unfold fwWheelWindowCutoff fwWheel15Cutoff
  rw [fw_wheel15_minima ⟨T % 8, Nat.mod_lt _ (by decide)⟩]

end
end Sude
