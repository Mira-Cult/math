import Shared.Beeping.NPcoNP.Source284InputCounterTransfer
import Shared.Beeping.NPcoNP.Source284CheckpointMarkedBounds
import Shared.Beeping.NPcoNP.Source284WitnessSeek

/-! The source-generated workspace counter has the parity required for the
existing witness seek: transferring it increases the saved witness gap by
whole pairs. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284InputCounterGeometry

open Shared.Beeping.NPcoNP.Source284CheckpointWorkspace
open Shared.Beeping.NPcoNP.Source284CheckpointMarkedWorkspace

theorem markCount_even (k r n : Nat) : markCount k r n % 2 = 0 := by
  have h := Source284GapUnarySource.history_cells_even r (extraOuter k n) (extraInner k n)
  unfold markCount cleanupZeros
  omega

theorem count_odd (k r n : Nat) : (markCount k r n-1)%2 = 1 := by
  have he := markCount_even k r n
  have hp := Source284CheckpointMarkedBounds.mark_count_large k r n
  omega

def extraPairs (k r n : Nat) : Nat := markCount k r n/2

theorem counter_length (k r n : Nat) : markCount k r n-1+1 = 2*extraPairs k r n := by
  have he := markCount_even k r n
  have hp := Source284CheckpointMarkedBounds.mark_count_large k r n
  have hd := Nat.mod_add_div (markCount k r n) 2
  unfold extraPairs
  omega

/-- Exact arithmetic for restoring the witness sentinel after transfer. The
new gap has `extraPairs` additional pairs; the witness frame is unchanged. -/
theorem enlarged_saved_frame (k r n limit witnessFrame : Nat) :
    2^((markCount k r n-1)+2)*(2*(4^(limit+1)*(2*witnessFrame)))+1 =
      4*(4^(limit+1+extraPairs k r n)*(2*witnessFrame))+1 := by
  have hc := counter_length k r n
  have he : (markCount k r n-1)+2 = 2*extraPairs k r n+1 := by omega
  rw [he,pow_succ,show limit+1+extraPairs k r n=(limit+1)+extraPairs k r n by omega,pow_add]
  have hp : 2^(2*extraPairs k r n) = 4^extraPairs k r n := by
    calc
      2^(2*extraPairs k r n) = (2^2)^(extraPairs k r n) := by rw [pow_mul]
      _ = 4^extraPairs k r n := by norm_num
  rw [hp]
  ring

/-- The additional paired gap is at least half the separately generated
counter size, uniformly in the input. -/
theorem counter_le_pairs (k r n : Nat) : markCount k r n-1 ≤ 2*extraPairs k r n := by
  have h := counter_length k r n
  omega

end Shared.Beeping.NPcoNP.Source284InputCounterGeometry
