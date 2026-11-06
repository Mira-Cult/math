import Shared.Beeping.NPcoNP.Source284SetLeftOne
import Shared.Beeping.NPcoNP.Source284ClearOddMarked
import Shared.Beeping.NPcoNP.Source284CountedShift

/-! Transfer a unary counter across a protected self-delimited input. The
counter is consumed in the actual finite table, adding its cells to the
saved-witness gap; both frame contents and the residual suffix are retained. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284InputCounterTransfer

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284DynamicInputFrame.clearTable (Source284ClearOddMarked.table
    (Source284CountedShift.table (Source284SetLeftOne.table
      (Source284ScratchNormalize.table (Source284PopContinue.table continuation)))))

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (178+states) (table continuation) := by
  have hp := Source284PopContinue.closed states continuation hn hv
  have hnorm := Source284WitnessReframe.closed (68+states) (Source284PopContinue.table continuation) (by omega) hp
  have hs := Source284SetLeftOne.closed (68+(68+states))
    (Source284ScratchNormalize.table (Source284PopContinue.table continuation)) (by omega) hnorm
  have hc := Source284CountedShift.closed (2+(68+(68+states)))
    (Source284SetLeftOne.table (Source284ScratchNormalize.table (Source284PopContinue.table continuation))) (by omega) hs
  have hm := Source284ClearOddMarked.closed (21+(2+(68+(68+states))))
    (Source284CountedShift.table (Source284SetLeftOne.table
      (Source284ScratchNormalize.table (Source284PopContinue.table continuation)))) (by omega) hc
  have hclear := Source284DynamicInputFrame.clear_closed (16+(21+(2+(68+(68+states)))))
    (Source284ClearOddMarked.table (Source284CountedShift.table (Source284SetLeftOne.table
      (Source284ScratchNormalize.table (Source284PopContinue.table continuation))))) (by omega) hm
  simpa [table,show 3+(16+(21+(2+(68+(68+states)))))=178+states by omega] using hclear

def cost (input : List Bool) (count : Nat) : Nat :=
  3+(8*(input++[false]).length+13)+((count+2)*(4*(input++[false]).length+7))+
    2+(6*(input++[false]).length+11)+(4*(input++[false]).length+12)

/-- The saved odd sentinel is cleared as one additional counter mark; the
counter and its terminating zero are then consumed to move zeros across the
whole input frame. Two transitions restore the sentinel before reframing. -/
theorem transfer_then (states : Nat) (continuation : Nat → Bool → Row)
    (input : List Bool) (certificate count higher fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    run (table continuation)
      ⟨2*(2*certificate+1)+1,flipped (input++[false]) (counter count higher),some 0⟩
      (cost input count+fuel) =
    shiftConfig 178 (run continuation
      ⟨2*(2^(count+2)*certificate+1),encodeFrame input (4*(2*higher+1)),some 0⟩ fuel) := by
  let W := input++[false]
  let norm := Source284ScratchNormalize.table (Source284PopContinue.table continuation)
  let h := counter count higher
  have ht : cost input count+fuel = 3+((8*W.length+13)+
      ((count+2)*(4*W.length+7)+(2+((6*W.length+11)+((4*W.length+12)+fuel))))) := by
    simp [cost,W]; omega
  rw [ht]
  change run (Source284DynamicInputFrame.clearTable (Source284ClearOddMarked.table
    (Source284CountedShift.table (Source284SetLeftOne.table norm))))
    ⟨2*(2*certificate+1)+1,flipped W h,some 0⟩ _ = _
  rw [Source284ScratchScanner.run_add,Source284DynamicInputFrame.clear_setup]
  change run (Source284DynamicInputFrame.clearTable (Source284ClearOddMarked.table
    (Source284CountedShift.table (Source284SetLeftOne.table norm))))
    (shiftConfig 3 ⟨2*certificate+1,2*flipped W h,some 0⟩) _ = _
  rw [Source284DynamicInputFrame.clear_run,Source284ClearOddMarked.clear_then]
  change shiftConfig 3 (shiftConfig 16 (run (Source284CountedShift.table (Source284SetLeftOne.table norm))
    ⟨certificate,2*flipped W (counter (count+1) higher),some 0⟩ _)) = _
  rw [Source284CountedShift.countdown_after]
  have he : 2^(count+1+1)*certificate = 2*(2^(count+1)*certificate) := by rw [pow_succ]; ring
  rw [he,Source284SetLeftOne.set_then]
  change _ = shiftConfig 178 (run continuation _ fuel)
  dsimp only [norm,W]
  rw [Source284WitnessReframe.normalize_then,
    Source284PopContinue.pop_then states continuation input false
      (2*(2*(2^(count+1)*certificate)+1)) (2*higher+1) fuel hn hv]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have hs : 3+16+14+1+6+2+68+68=178 := by omega
  rw [hs]
  have hp : 2*(2^(count+1)*certificate) = 2^(count+2)*certificate := by
    rw [show count+2=count+1+1 by omega,pow_succ]; ring
  rw [hp]
  simp [bit]

end Shared.Beeping.NPcoNP.Source284InputCounterTransfer
