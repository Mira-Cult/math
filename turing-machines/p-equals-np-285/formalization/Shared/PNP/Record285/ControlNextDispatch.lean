import Shared.PNP.Record285.ControlBreakComplete
import Shared.PNP.Record285.ControlContinueComplete
import Shared.PNP.Record285.HalfNextDispatch

/-! Compose completed control leaves with the next actual-tape dispatch. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ControlNextDispatch
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.HalfComplete (NextDispatch returned_root_dispatch)

theorem continue_result_dispatch (code : List Bool) (i : Nat) (marker : Bool)
    (head : Int) (leftTail rightTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (h : ControlContinue.Result code i marker head leftTail rightTail physical) : NextDispatch physical := by
  obtain ⟨pre,hcode,h⟩ := h
  cases i with
  | zero => contradiction
  | succ i =>
    cases i with
    | zero =>
      rcases h with ⟨_,hr⟩
      exact returned_root_dispatch _ _ _ _ physical hr
    | succ i =>
      cases i with
      | zero =>
        rcases h with ⟨_,hr⟩
        exact returned_root_dispatch _ _ _ _ physical hr
      | succ i => contradiction

theorem break_result_dispatch (code : List Bool) (i gap : Nat) (head : Int) (leftTail bank : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (h : ControlBreak.Result code i gap head leftTail bank physical) : NextDispatch physical := by
  obtain ⟨pre,hcode,h⟩ := h
  cases i with
  | zero =>
    rcases h with ⟨_,hr⟩
    exact returned_root_dispatch _ _ _ _ physical hr
  | succ i =>
    cases i with
    | zero =>
      rcases h with ⟨_,hr⟩
      exact returned_root_dispatch _ _ _ _ physical hr
    | succ i =>
      cases i with
      | zero =>
        rcases h with ⟨_,hr⟩
        exact returned_root_dispatch _ _ _ _ physical hr
      | succ i => contradiction

/-- Every continuation is followed by a second positive, silent physical
dispatcher segment on the resulting tape. -/
theorem continue_then_dispatch (code : List Bool) (i : Nat) (hwalk : walk 162 code = some (.cont i))
    (marker : Bool) (head : Int) (leftTail rightTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail)
      physical) :
    ∃ steps, 0 < steps ∧
      ControlContinue.Result code i marker head leftTail rightTail
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      NextDispatch ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨steps,hpos,hresult,hquiet⟩ :=
    ControlContinue.root_continue_complete code i hwalk marker head leftTail rightTail physical hrel
  exact ⟨steps,hpos,hresult,continue_result_dispatch code i marker head leftTail rightTail _ hresult,hquiet⟩

/-- Every break is followed by a second positive, silent physical dispatcher
segment under the same explicit anchor condition. -/
theorem break_then_dispatch (code : List Bool) (i : Nat) (hwalk : walk 162 code = some (.brk i))
    (marker : Bool) (gap : Nat) (head : Int) (leftTail rightTail bank : Nat)
    (hanchor : bitVal marker+2*rightTail = runPattern false gap true (2*bank))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail)
      physical) :
    ∃ steps, 0 < steps ∧
      ControlBreak.Result code i gap head leftTail bank
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      NextDispatch ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨steps,hpos,hresult,hquiet⟩ :=
    ControlBreak.root_break_complete code i hwalk marker gap head leftTail rightTail bank hanchor physical hrel
  exact ⟨steps,hpos,hresult,break_result_dispatch code i gap head leftTail bank _ hresult,hquiet⟩

/-- Only break leaves require a finite right-hand anchor and delimiter. -/
def ControlPremise (e : Edge) (marker : Bool) (rightTail : Nat) : Prop :=
  match e with
  | .cont _ => True
  | .brk _ => ∃ gap bank, bitVal marker+2*rightTail = runPattern false gap true (2*bank)
  | _ => False

def ControlResult (code : List Bool) (e : Edge) (marker : Bool) (head : Int)
    (leftTail rightTail : Nat) (out : Shared.Beeping.Machines.Config 285) : Prop :=
  match e with
  | .cont i => ControlContinue.Result code i marker head leftTail rightTail out
  | .brk i => ∃ gap bank, bitVal marker+2*rightTail = runPattern false gap true (2*bank) ∧
      ControlBreak.Result code i gap head leftTail bank out
  | _ => False

/-- Unified progress-sensitive interface for any break or continuation
grammar leaf, retaining the operation-specific anchor premise. -/
theorem control_then_dispatch (code : List Bool) (e : Edge) (hwalk : walk 162 code = some e)
    (marker : Bool) (head : Int) (leftTail rightTail : Nat)
    (hpremise : ControlPremise e marker rightTail) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail)
      physical) :
    ∃ steps, 0 < steps ∧
      ControlResult code e marker head leftTail rightTail
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      NextDispatch ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  cases e with
  | node i => contradiction
  | inc i => contradiction
  | dec i => contradiction
  | half i => contradiction
  | beep => contradiction
  | cont i => exact continue_then_dispatch code i hwalk marker head leftTail rightTail physical hrel
  | brk i =>
    obtain ⟨gap,bank,hanchor⟩ := hpremise
    obtain ⟨steps,hpos,hresult,hnext,hquiet⟩ :=
      break_then_dispatch code i hwalk marker gap head leftTail rightTail bank hanchor physical hrel
    exact ⟨steps,hpos,⟨gap,bank,hanchor,hresult⟩,hnext,hquiet⟩

end Shared.PNP.Record285.ControlNextDispatch
