import Shared.Codes.FinitePrograms
import Shared.Beeping.ComparisonImplementation

/-! A conditional connection to a future finite beeping machine. Supplying the
certificate requires proving finite, event-correct comparison execution; no
such implementation or canonical complexity bridge is assumed here. -/
namespace Shared.Codes.FinitePrograms

theorem certified_machine_silent_iff {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate compareSAT 0 M) :
    M.system.EventuallySilent ↔ ∃ c : Candidate, valid c.2 = true ∧
      ∀ input, evaluate c (BitstringEncoding.bitEncode input) = some (Shared.ComplexityBridge.CNF.sat input) := by
  calc
    M.system.EventuallySilent ↔ ∃ e, Shared.Beeping.Controller.Good compareSAT e := by
      simpa using cert.eventuallySilent_iff_good
    _ ↔ (Shared.Beeping.Controller.system compareSAT 0).EventuallySilent :=
      (Shared.Beeping.Controller.eventuallySilent_zero_iff_exists_good compareSAT).symm
    _ ↔ _ := controller_silent_iff

end Shared.Codes.FinitePrograms
