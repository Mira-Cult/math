import PASoundness.M236RuntimeCertificate

/-! A readable complete tape description for the certified runtime entry. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace PASoundness.M236.RuntimeGeometry

open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.BulkSweep PASoundness.M236.PackedTape
open PASoundness.M236.FiniteTape PASoundness.M236.RuntimeCertificate

/-- Nearest-left first. The right side has 3,821 zeros followed by 1,910
`1,0` pairs; all omitted cells are zero. -/
def entryTape : FiniteTape.Tape :=
  ⟨[false, true, true, false, false, false, false, false, false, false],
    List.replicate 3820 false ++ (false :: pairs true false 1910)⟩

theorem entry_tape_checked : (unpackConfig Part66.state3).tape = entryTape := by
  rfl

/-- Literal selected-machine runtime entry from blank, with the entire tape
and the complete preceding output prefix. -/
theorem selected_entry_geometry :
    Related ⟨78, -3818, entryTape⟩ ((machineWordSystem machine machineLabels).run 89821408) ∧
      (machineWordSystem machine machineLabels).prefixWord 89821408 = [] := by
  have h := selected_entry
  rw [entry_tape_checked] at h
  exact h

end PASoundness.M236.RuntimeGeometry
