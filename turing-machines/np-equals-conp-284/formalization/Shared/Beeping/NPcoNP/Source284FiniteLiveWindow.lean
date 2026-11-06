import Shared.Beeping.NPcoNP.Source284EncoderSourceWindow

/-! Reflect a live bounded run through the compiled source's finite-window
simulation. A matching live control cannot be a terminal result or reject
sink, so the actual finite program has a live run too. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284FiniteLiveWindow

open Shared.Codes.FinitePrograms
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284CompileRecords (compile codeState rejectState)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284FiniteProgramRun (Related)

/-- A live control for a real program state cannot be a terminal or sink
control. It also uniquely identifies the finite state and orientation. -/
theorem related_live_of_state (p : Program) (status : Status) (c : Source284Relative.Config)
    (q : Nat) (rev : Bool) (hq : q < p.length)
    (hrel : Related p status c) (hc : c.state = codeState q rev) :
    ∃ tape, status = some (.inr (q,tape)) ∧ c = represented tape rev (codeState q rev) := by
  cases hrel with
  | live q' tape rev' hq' =>
    simp only [Source284FiniteTapeStep.represented_state] at hc
    cases rev <;> cases rev' <;>
      simp [codeState,Source284CompileRecords.bit] at hc <;>
      try omega
    all_goals
      have he : q' = q := by omega
      subst q'
      exact ⟨tape,rfl,rfl⟩
  | yes c h =>
    rw [h] at hc
    have hp := Source284CompileRecords.state_positive q rev
    omega
  | no c h =>
    rw [h] at hc
    cases rev <;> simp [rejectState,codeState,Source284CompileRecords.bit] at hc <;> omega
  | invalid c h =>
    rw [h] at hc
    cases rev <;> simp [rejectState,codeState,Source284CompileRecords.bit] at hc <;> omega

/-- If a valid finite program has a live reference run, matching the initial
source window through `k+d` forces a live actual finite run at the same clock
and the same finite control. The final represented tapes agree on `k` cells. -/
theorem live_run_of_window (program : Program) (input : List Bool) (initialTape : Tape)
    (d k q : Nat) (referenceTape : Tape)
    (hv : valid program = true)
    (hrun : run program (initial input) d = some (.inr (q,referenceTape)))
    (hw : Window (k+d) (represented initialTape false (codeState 0 false))
      (Source284Relative.initial (value input) 0)) :
    ∃ actualTape rev,
      run program (0,initialTape) d = some (.inr (q,actualTape)) ∧
      Window k (represented actualTape rev (codeState q rev))
        (represented referenceTape rev (codeState q rev)) := by
  have hn : 0 < program.length := Shared.Codes.FiniteProgramLink.valid_nonempty program hv
  have hq : q < program.length := by
    have hh := Shared.Codes.FiniteProgramLink.run_in_range program hv (initial input) (by simpa [initial] using hn) d
    rw [hrun] at hh
    exact hh
  obtain ⟨rev,hwindow⟩ := Source284EncoderSourceWindow.compiled_live_window program input d k q referenceTape
    (represented initialTape false (codeState 0 false)) hv hrun hw
  have hrelated := Source284FiniteProgramRun.run_related program
    (Source284FiniteProgramRun.closed_of_valid program hv) 0 initialTape false hn d
  have hstate := hwindow.1
  simp only [Source284FiniteTapeStep.represented_state] at hstate
  obtain ⟨actualTape,hr,hs⟩ := related_live_of_state program _ _ q rev hq hrelated hstate
  rw [hs] at hwindow
  exact ⟨actualTape,rev,hr,hwindow⟩

end Shared.Beeping.NPcoNP.Source284FiniteLiveWindow
