import Shared.Beeping.NPcoNP.Source284CheckpointCost
import Shared.Beeping.NPcoNP.Source284EraseMarkedHistory
import Shared.Beeping.NPcoNP.Source284ScratchCounterExtendThen

/-! Record the extra workspace cleanup as a unary counter behind a distinct
zero separator. One guard-side zero supplies the separator; one separately
paid counter extension restores the guard's mark count. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284CheckpointMarkedWorkspace

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284ProductIteration
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284CheckpointWorkspace
open Shared.Beeping.NPcoNP.Source284ScratchMarkedLoop (marks)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)

def markCount (k r n : Nat) : Nat :=
  Source284EraseTokenHistory.cells r (extraOuter k n) (extraInner k n)+cleanupZeros k r n+2

def blankTail (k r n suffix : Nat) : Nat :=
  let first := suffixAfter k (base n) (base n) (Source284SentinelPositiveTokens.retained n suffix)
  let second := suffixAfter (r+2) (previous k n) (guard k n) first
  2^(workspace k r n+1)*halves (workspace k r n) (second/2)

def shortHistory (k n certificate : Nat) : Nat :=
  2^(2*guard k n)*(2*pairTape (List.replicate (previous k n) false)
    (historyAfter k (base n) (base n) (2*certificate+1))+1)

def higher (k r n suffix : Nat) : Nat := marks (markCount k r n) (blankTail k r n suffix)/2

def table (k r : Nat) (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ProductIteration.table k
    (Source284ProductIteration.table (r+2)
      (Source284TwoSidedWorkspace.table (Source284EraseMarkedBlock.table
        (Source284EraseMarkedHistory.table r (Source284ScratchCompactOne.table
          (Source284ScratchCounterExtend.table continuation))))))

def description (k r states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284SentinelPositiveTokens.description
    (287*k+(287*(r+2)+(73+(30+(30*r+(14+(16+states))))))) (table k r continuation)

def totalCost (k r : Nat) (w : List Bool) : Nat :=
  Source284CheckpointWorkspace.totalCost k r w+(8*(w++[false]).length+11)+(4*(w++[false]).length+16)

theorem closed (k r states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (287*k+(287*(r+2)+(73+(30+(30*r+(14+(16+states))))))) (table k r continuation) := by
  have he := Source284ScratchCounterExtend.closed states continuation hn hv
  have hc := Source284ScratchCompactOne.closed (16+states)
    (Source284ScratchCounterExtend.table continuation) (by omega) he
  have hh := Source284EraseMarkedHistory.closed r (14+(16+states))
    (Source284ScratchCompactOne.table (Source284ScratchCounterExtend.table continuation)) (by omega) hc
  have hz := Source284EraseMarkedBlock.closed (30*r+(14+(16+states)))
    (Source284EraseMarkedHistory.table r (Source284ScratchCompactOne.table
      (Source284ScratchCounterExtend.table continuation))) (by omega) hh
  have hw := Source284TwoSidedWorkspace.closed (30+(30*r+(14+(16+states))))
    (Source284EraseMarkedBlock.table (Source284EraseMarkedHistory.table r
      (Source284ScratchCompactOne.table (Source284ScratchCounterExtend.table continuation)))) (by omega) hz
  have hp := Source284ProductIteration.closed (r+2) (73+(30+(30*r+(14+(16+states)))))
    (Source284TwoSidedWorkspace.table (Source284EraseMarkedBlock.table
      (Source284EraseMarkedHistory.table r (Source284ScratchCompactOne.table
        (Source284ScratchCounterExtend.table continuation))))) (by omega) hw
  exact Source284ProductIteration.closed k _ _ (by omega) hp

/-- All marks are created by the actual finite cleanup. The separator is
created by consuming one low zero from the guard history; extending the
initial counter then installs one compensating mark before the separator. -/
theorem source_then (k r states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k r states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost k r w+fuel) =
    toSource (shiftConfig (1282+287*k+317*r) (run continuation
      ⟨shortHistory k w.length certificate,
        2*flipped (w++[false]) (counter 1 (higher k r w.length suffix)),some 0⟩ fuel)) := by
  let n := w.length
  let a := previous k n
  let b := guard k n
  let m := workspace k r n
  let outer := workspaceOuter k r n
  let z := cleanupZeros k r n
  let old := historyAfter k (base n) (base n) (2*certificate+1)
  let first := suffixAfter k (base n) (base n) (Source284SentinelPositiveTokens.retained n suffix)
  let second := suffixAfter (r+2) a b first
  let c1 := cost k (base n) (base n) (w++[false]).length
  let c2 := cost (r+2) a b (w++[false]).length
  let cw := Source284TwoSidedWorkspace.workCost m (w++[false]).length
  let cz := Source284EraseZeroBlock.cost z (w++[false]).length
  let ch := Source284EraseTokenHistory.cost r (extraOuter k n) (extraInner k n) (w++[false]).length
  let cs := 8*(w++[false]).length+11
  let ce := 4*(w++[false]).length+16
  have hc := closed k r states continuation hn hv
  have h := Source284SentinelPositiveTokens.source_then
    (287*k+(287*(r+2)+(73+(30+(30*r+(14+(16+states))))))) (table k r continuation)
    w certificate suffix (c1+(c2+(cw+(cz+(ch+(cs+(ce+fuel))))))) (by omega) hc
  have ht : totalCost k r w+fuel = Source284SentinelPositiveTokens.totalCost w+
      (c1+(c2+(cw+(cz+(ch+(cs+(ce+fuel))))))) := by
    simp [totalCost,Source284CheckpointWorkspace.totalCost,n,a,b,m,z,c1,c2,cw,cz,ch,cs,ce]; omega
  rw [ht]
  change Source284Relative.run (Source284SentinelPositiveTokens.description _ (table k r continuation)) _ _ = _
  rw [h]
  change toSource (shiftConfig 575 (run (Source284ProductIteration.table k
    (Source284ProductIteration.table (r+2) (Source284TwoSidedWorkspace.table
      (Source284EraseMarkedBlock.table (Source284EraseMarkedHistory.table r
        (Source284ScratchCompactOne.table (Source284ScratchCounterExtend.table continuation)))))))
    ⟨pairTape (List.replicate (base n) false) (pairTape (List.replicate (base n) false) (2*certificate+1)),
      2*flipped (w++[false]) (Source284SentinelPositiveTokens.retained n suffix),some 0⟩ _)) = _
  rw [Source284ProductIteration.iterate_then]
  change toSource (shiftConfig 575 (shiftConfig (287*k) (run
    (Source284ProductIteration.table (r+2) (Source284TwoSidedWorkspace.table
      (Source284EraseMarkedBlock.table (Source284EraseMarkedHistory.table r
        (Source284ScratchCompactOne.table (Source284ScratchCounterExtend.table continuation))))))
    ⟨pairTape (List.replicate b false) (pairTape (List.replicate a false) old),
      2*flipped (w++[false]) first,some 0⟩ _))) = _
  rw [Source284ProductIteration.iterate_then]
  change toSource (shiftConfig 575 (shiftConfig (287*k) (shiftConfig (287*(r+2)) (run
    (Source284TwoSidedWorkspace.table (Source284EraseMarkedBlock.table (Source284EraseMarkedHistory.table r
      (Source284ScratchCompactOne.table (Source284ScratchCounterExtend.table continuation)))))
    ⟨pairTape (List.replicate m false) (pairTape (List.replicate outer false) (historyAfter (r+2) a b old)),
      2*flipped (w++[false]) second,some 0⟩ _)))) = _
  rw [Source284TwoSidedWorkspace.workspace_then,Source284PolynomialRunwayCleanup.top_form]
  change toSource (shiftConfig 575 (shiftConfig (287*k) (shiftConfig (287*(r+2)) (shiftConfig 73
    (run (Source284EraseMarkedBlock.table (Source284EraseMarkedHistory.table r
      (Source284ScratchCompactOne.table (Source284ScratchCounterExtend.table continuation))))
      ⟨2^(z+1)*(2*historyAfter (r+2) a b old+1),_,some 0⟩ _))))) = _
  rw [Source284EraseMarkedBlock.erase_then,Source284CheckpointWorkspace.checkpoint_history]
  have hch : ch = Source284EraseTokenHistory.cost r (a*b) (b*(a*b)) (w++[false]).length := rfl
  rw [hch,Source284EraseMarkedHistory.erase_then,Source284EraseMarkedHistory.marks_add]
  rw [Source284EraseTokenHistory.block_form]
  have hp : 2^(2*b+1)*(2*pairTape (List.replicate a false) old+1) =
      2*(2^(2*b)*(2*pairTape (List.replicate a false) old+1)) := by rw [pow_succ]; ring
  rw [hp,Source284ScratchCompactOne.compact_after]
  change _ = toSource (shiftConfig (1282+287*k+317*r) (run continuation _ fuel))
  change toSource (shiftConfig 575 (shiftConfig (287*k) (shiftConfig (287*(r+2)) (shiftConfig 73
    (shiftConfig 30 (shiftConfig (30*r) (shiftConfig 14 (run
      (Source284ScratchCounterExtend.table continuation)
      ⟨_,2*flipped (w++[false]) (counter 0 (marks (markCount k r n) (blankTail k r n suffix))),some 0⟩ _)))))))) = _
  rw [Source284ScratchCounterExtendThen.extend_then]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have he : 575+287*k+287*(r+2)+73+30+30*r+14+16=1282+287*k+317*r := by omega
  rw [he]
  rfl

end Shared.Beeping.NPcoNP.Source284CheckpointMarkedWorkspace
