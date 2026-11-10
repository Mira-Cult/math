import PASoundness.M236UnaryShift
import PASoundness.M236RuntimeGeometry

/-!
The certified blank-start tape contains the unary zero-block pattern used by
the shift lemmas. The 1,910 blocks describe this one initial geometry; they
are not a bound on later values or on the amount of tape used.
-/
namespace PASoundness.M236.UnaryEntry

open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

def entryBankTape : Tape :=
  ⟨[false, true, true, false, false, false, false, false, false, false],
    List.replicate 3820 false ++ (false :: bank (List.replicate 1910 0))⟩

theorem entry_tape_bank : RuntimeGeometry.entryTape = entryBankTape := by
  simp only [RuntimeGeometry.entryTape, entryBankTape, bank_zeros]

/-- Literal selected-machine blank execution reaches the displayed bank
pattern with no earlier event. This does not identify logical register names. -/
theorem selected_initial_bank :
    Related ⟨78, -3818, entryBankTape⟩
      ((machineWordSystem machine machineLabels).run 89821408) ∧
      (machineWordSystem machine machineLabels).prefixWord 89821408 = [] := by
  have h := RuntimeGeometry.selected_entry_geometry
  rw [entry_tape_bank] at h
  exact h

end PASoundness.M236.UnaryEntry
