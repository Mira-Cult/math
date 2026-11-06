import Shared.Beeping.NPcoNP.Source284DropPayloadSentinel
import Shared.Beeping.NPcoNP.Source284ScratchNormalize

/-! Remove the extra payload sentinel, then run the existing finite frame
normalizer. The entire unary/certificate half remains on the tape. -/
namespace Shared.Beeping.NPcoNP.Source284PrepareFrame

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284DropPayloadSentinel.table (Source284ScratchNormalize.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (80+states) (table continuation) := by
  have hnrm := Source284ScratchNormalize.closed states continuation hn hv
  have heq : 36+(32+states) = 68+states := by omega
  rw [heq] at hnrm
  have hnrm' : Closed (68+states) (Source284ScratchNormalize.table continuation) := hnrm
  have hd := Source284DropPayloadSentinel.closed (68+states)
    (Source284ScratchNormalize.table continuation) (by omega) hnrm'
  have he : 12+(68+states) = 80+states := by omega
  rw [he] at hd
  exact hd

/-- The low frame encodes the original payload, not the extra false sentinel.
The two zero cells formerly above the sentinel remain in the high suffix. -/
theorem prepare (continuation : Nat → Bool → Row) (w : List Bool) (left tail : Nat) :
    run (table continuation) ⟨left,2*flipped (w++[false]) tail,some 0⟩ (10*w.length+21) =
      ⟨2*left,encodeFrame w (8*tail+1),some 80⟩ := by
  have ht : 10*w.length+21 = (4*w.length+10)+(6*w.length+11) := by omega
  rw [ht,run_add]
  unfold table
  rw [Source284DropPayloadSentinel.drop]
  change run (Source284DropPayloadSentinel.table (Source284ScratchNormalize.table continuation))
    (shiftConfig 6 (shiftConfig 6 ⟨left,2*flipped w (4*tail),some 0⟩)) _ = _
  rw [Source284DropPayloadSentinel.relocated_run,Source284ScratchFlipReturn.relocated_run,
    Source284ScratchNormalize.normalize]
  have he : 2*(4*tail)+1 = 8*tail+1 := by omega
  simp [shiftConfig,he]

/-- The supplied finite continuation executes after both conversions, with
all eighty prefix states accounted for. -/
theorem continuation_run (continuation : Nat → Bool → Row) (mode : Nat) (left right fuel : Nat) :
    run (table continuation) ⟨left,right,some (80+mode)⟩ fuel =
      shiftConfig 6 (shiftConfig 6 (shiftConfig 36 (shiftConfig 32
        (run continuation ⟨left,right,some mode⟩ fuel)))) := by
  let c : Config := ⟨left,right,some mode⟩
  have he : shiftConfig 6 (shiftConfig 6 (shiftConfig 36 (shiftConfig 32 c))) =
      ⟨left,right,some (80+mode)⟩ := by simp [shiftConfig,c,← Nat.add_assoc]
  rw [← he]
  unfold table
  rw [Source284DropPayloadSentinel.relocated_run,Source284ScratchFlipReturn.relocated_run,
    Source284ScratchNormalize.relocated_run,Source284ModePrefixReturn.relocated_run]

end Shared.Beeping.NPcoNP.Source284PrepareFrame
