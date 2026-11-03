import Shared.PNP.Record285.ControlBreakTwo

/-! One root-to-root contract for all literal grammar break levels. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ControlBreak
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar

/-- Branch-specific full physical result, including exact control successor. -/
def Result (code : List Bool) (i gap : Nat) (head : Int) (leftTail bank : Nat)
    (out : Shared.Beeping.Machines.Config 285) : Prop :=
  ∃ pre, code = pre++[true] ∧
    let p := peel pre.reverse
    let q := peel p.2
    let r := peel q.2
    match i with
    | 0 =>
      let precode := p.2.reverse
      returnPath code = some (precode++[true]) ∧
      Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-2-p.1) leftTail (runPattern false (p.1+gap) true (2*bank))) out
    | 1 =>
      let precode := q.2.reverse
      returnPathSkipOne code = some (precode++[true]) ∧
      Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-2-p.1-1-q.1) leftTail (runPattern false (q.1+(p.1+gap+1)) true (2*bank))) out
    | 2 =>
      let precode := r.2.reverse
      returnPathSkipTwo code = some (precode++[true]) ∧
      Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-2-p.1-1-q.1-1-r.1) leftTail
        (runPattern false (r.1+(q.1+(p.1+gap+1)+1)) true (2*bank))) out
    | _ => False

/-- All grammar break leaves complete silently in finite positive time when
the full following tape has the explicit finite anchor-and-delimiter layout. -/
theorem root_break_complete (code : List Bool) (i : Nat) (hwalk : walk 162 code = some (.brk i))
    (marker : Bool) (gap : Nat) (head : Int) (leftTail rightTail bank : Nat)
    (hanchor : bitVal marker+2*rightTail = runPattern false gap true (2*bank))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail)
      physical) :
    ∃ steps, 0 < steps ∧
      Result code i gap head leftTail bank
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  cases i with
  | zero =>
    obtain ⟨pre,hcode,hpath,hend,hquiet,hpos⟩ :=
      root_break_zero_physical code hwalk marker gap head leftTail rightTail bank hanchor physical hrel
    exact ⟨_,hpos,⟨pre,hcode,hpath,hend⟩,hquiet⟩
  | succ i =>
    cases i with
    | zero =>
      obtain ⟨pre,hcode,hpath,hend,hquiet,hpos⟩ :=
        root_break_one_physical code hwalk marker gap head leftTail rightTail bank hanchor physical hrel
      exact ⟨_,hpos,⟨pre,hcode,hpath,hend⟩,hquiet⟩
    | succ i =>
      cases i with
      | zero =>
        obtain ⟨pre,hcode,hpath,hend,hquiet,hpos⟩ :=
          root_break_two_physical code hwalk marker gap head leftTail rightTail bank hanchor physical hrel
        exact ⟨_,hpos,⟨pre,hcode,hpath,hend⟩,hquiet⟩
      | succ i =>
        obtain ⟨_,_,row,_,_,_,hexpected,_,_⟩ := ControlInvariant.break_prefix_safe code (i+3) (by simpa using hwalk)
        simp [expected,breakTerminal] at hexpected

end Shared.PNP.Record285.ControlBreak
