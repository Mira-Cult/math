import Shared.Beeping.NPcoNP.Source284PayloadSentinelPipeline

/-! Exact relocation of source configurations, including absorbing
acceptance. This strengthens the witness-conversion handoff from acceptance
agreement to equality of both tape halves and the relocated source state. -/
set_option maxRecDepth 4096
namespace Shared.Beeping.NPcoNP.Source284SourceRelocation

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

/-- A source-code state offset preserves the absorbing zero state. -/
def lift (d : Nat) (c : Source284Relative.Config) : Source284Relative.Config :=
  ⟨c.left,c.right,if c.state = 0 then 0 else c.state+2*d⟩

theorem lift_toSource (d : Nat) (c : Config) :
    lift d (toSource c) = toSource (shiftConfig d c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp [lift,toSource,shiftConfig,nextState,active,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem shiftConfig_add (d e : Nat) (c : Config) :
    shiftConfig d (shiftConfig e c) = shiftConfig (d+e) c := by
  cases c with
  | mk left right state =>
    cases state <;> simp [shiftConfig,Nat.add_assoc]

theorem lift_active (d left right q : Nat) :
    lift d ⟨left,right,active q⟩ = ⟨left,right,active (d+q)⟩ := by
  simp [lift,active,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem lift_add (a b : Nat) (c : Source284Relative.Config) :
    lift a (lift b c) = lift (a+b) c := by
  cases c with
  | mk left right state =>
    by_cases h : state = 0
    · simp [lift,h]
    · simp [lift,h] <;> omega

/-- Every continuation step after raw frame conversion is simulated in the
same encoded source table, with exact tape halves and state relocation. -/
theorem source_run_after_pipeline (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix clock : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (Source284PayloadSentinelPipeline.description states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate)
      (Source284PayloadSentinelPipeline.totalCost w.length+clock) =
    lift 155 (Source284Relative.run (encode states continuation 1)
      (Source284Relative.initial (2*flipped (w++[false]) ((suffix/4)/4)) certificate) clock) := by
  let c : Config := ⟨certificate,2*flipped (w++[false]) ((suffix/4)/4),some 0⟩
  have hc := Source284PayloadSentinel.closed states continuation hn hv
  have h0 : Valid states c := by intro q hq; simp [c] at hq; subst q; exact hn
  have h1 : Valid (142+(13+states))
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 (shiftConfig 7 (shiftConfig 6 c))))))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr1 := run_toSource (142+(13+states))
    (Source284ScratchFlipPipeline.table (Source284PayloadSentinel.table continuation)) 1
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
      (shiftConfig 3 (shiftConfig 6 (shiftConfig 7 (shiftConfig 6 c)))))))))
    (Source284ScratchFlipPipeline.closed (13+states) (Source284PayloadSentinel.table continuation)
      (by omega) hc) h1 clock
  have hr0 := run_toSource states continuation 1 c hv h0 clock
  change Source284Relative.run (Source284PayloadSentinelPipeline.description states continuation)
    ⟨certificate,2*flipped (w++[false]) ((suffix/4)/4),
      active (8+(8+(16+(32+(69+(3+(6+(7+6))))))))⟩ clock = _ at hr1
  have hs : 8+(8+(16+(32+(69+(3+(6+(7+6))))))) = 155 := by omega
  rw [hs] at hr1
  change Source284Relative.run (encode states continuation 1)
    (Source284Relative.initial (2*flipped (w++[false]) ((suffix/4)/4)) certificate) clock = _ at hr0
  rw [Source284Relative.run_add_clock,
    Source284PayloadSentinelPipeline.source_pipeline states continuation w certificate suffix hn hv,hr1,hr0]
  change toSource (run (Source284InputSentinel.table
    (Source284ModePrefixScan.table (Source284ScratchTerminator.table
      (Source284PayloadLoop.table (Source284ScratchFlip.table (Source284ScratchFlipReturn.table
        (Source284PayloadSentinel.table continuation)))))))
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
      (shiftConfig 3 (shiftConfig 6 (shiftConfig 7 (shiftConfig 6 c))))))))) clock) = _
  rw [Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    Source284ScratchTerminator.relocated_run,Source284ModePrefixReturn.relocated_run,
    Source284PayloadLoop.relocated_run,Source284ScratchFlip.relocated_run,
    Source284ScratchFlipReturn.relocated_run,Source284PayloadSentinel.relocated_run,
    Source284ScratchFlipReturn.relocated_run,lift_toSource]
  simp only [shiftConfig_add]

end Shared.Beeping.NPcoNP.Source284SourceRelocation
