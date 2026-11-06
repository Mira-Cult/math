import Shared.Beeping.NPcoNP.Source284TokenCounterLoop

/-! The exhaustion branch executes the supplied finite continuation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284TokenCounterContinue

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig shiftRow)

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    Source284TokenCounterLoop.table continuation (32+q) b = shiftRow 32 (continuation q b) := by
  have hn : 32+q ≠ 31 := by omega
  simp only [Source284TokenCounterLoop.table,hn,if_false,Source284TokenCounterRound.table]
  have he : 32+q = 12+(4+(4+(5+(1+(6+q))))) := by omega
  rw [he,Source284UnaryMarkOne.relocated_row,Source284TokenCounterRound.dispatch_relocated_row,
    Source284ScratchCounterExtend.relocated_row,Source284CounterExtend.relocated_row]
  simp only [Source284ScratchCounterSeed.afterSeed,show 1+(6+q) ≠ 0 by omega,if_false,
    show 1+(6+q)-1 = 6+q by omega,Source284ScratchFlipReturn.relocated_row]
  cases h : (continuation q b).next <;> simp [shiftRow,h,← Nat.add_assoc]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (Source284TokenCounterLoop.table continuation) (shiftConfig 32 c) =
      shiftConfig 32 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (Source284TokenCounterLoop.table continuation) (shiftConfig 32 c) fuel =
      shiftConfig 32 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

end Shared.Beeping.NPcoNP.Source284TokenCounterContinue
