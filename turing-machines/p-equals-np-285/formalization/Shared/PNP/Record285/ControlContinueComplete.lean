import Shared.PNP.Record285.ControlContinueTwo

/-! One root-to-root contract for both grammar continuation levels. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ControlContinue
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar

def Result (code : List Bool) (i : Nat) (marker : Bool) (head : Int) (leftTail rightTail : Nat)
    (out : Shared.Beeping.Machines.Config 285) : Prop :=
  ∃ pre, code = pre++[true] ∧
    let p := peelZeros pre.reverse
    let q := peelZeros p.2
    let right := bitVal marker+2*rightTail
    match i with
    | 1 =>
      let precode := p.2.reverse
      continuePathOne code = some (precode++[true]) ∧
      Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-2-p.1) leftTail (pushBit p.1 false right)) out
    | 2 =>
      let precode := q.2.reverse
      let mid := 2*pushBit p.1 false right
      continuePathTwo code = some (precode++[true]) ∧
      Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-2-p.1-1-q.1) leftTail (pushBit q.1 false mid)) out
    | _ => False

/-- Every grammar continuation reaches the next root in finite positive time
without an event, with either following bit and arbitrary full tape tails. -/
theorem root_continue_complete (code : List Bool) (i : Nat) (hwalk : walk 162 code = some (.cont i))
    (marker : Bool) (head : Int) (leftTail rightTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail)
      physical) :
    ∃ steps, 0 < steps ∧
      Result code i marker head leftTail rightTail
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  cases i with
  | zero =>
    obtain ⟨_,_,row,_,_,_,hexpected,_,_⟩ := ControlInvariant.continue_prefix_safe code 0 hwalk
    simp [expected,continueTerminal] at hexpected
  | succ i =>
    cases i with
    | zero =>
      obtain ⟨pre,hcode,hpath,hend,hquiet,hpos⟩ :=
        root_continue_one_any_physical code hwalk marker head leftTail rightTail physical hrel
      exact ⟨_,hpos,⟨pre,hcode,hpath,hend⟩,hquiet⟩
    | succ i =>
      cases i with
      | zero =>
        obtain ⟨pre,hcode,hpath,hend,hquiet,hpos⟩ :=
          root_continue_two_any_physical code hwalk marker head leftTail rightTail physical hrel
        exact ⟨_,hpos,⟨pre,hcode,hpath,hend⟩,hquiet⟩
      | succ i =>
        obtain ⟨_,_,row,_,_,_,hexpected,_,_⟩ :=
          ControlInvariant.continue_prefix_safe code (i+3) (by simpa using hwalk)
        simp [expected,continueTerminal] at hexpected

end Shared.PNP.Record285.ControlContinue
