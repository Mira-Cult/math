import Shared.Beeping.NPcoNP.Bootstrap284SecondIncrementReturn

/-! The exact reachable unit-entry tape has an unbounded blank right ray.
This is a blank-start finite-prefix fact, not a global execution invariant. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284SecondBlankRay
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
open Shared.Beeping.NPcoNP.Bootstrap284TerminalUnit
open Shared.Beeping.NPcoNP.Bootstrap284ManyShift
open Shared.Beeping.NPcoNP.Bootstrap284ManyCarry
open Shared.Beeping.NPcoNP.Bootstrap284UnitWindow83
open Shared.Beeping.NPcoNP.Bootstrap284AllZeroReturn
open Shared.Beeping.NPcoNP.Bootstrap284TerminalFullExact
open Shared.Beeping.NPcoNP.Bootstrap284NextBankExact
open Shared.Beeping.NPcoNP.Bootstrap284NextReturnExact
open Shared.Beeping.NPcoNP.Bootstrap284SecondAllZeroExact
open Shared.Beeping.NPcoNP.Bootstrap284SecondIncrementReturn

set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- All cells from 12 onward are blank in the state-12 input tape. -/
theorem input_right_blank (q : Int) (hq : 12≤q) : inputTape q=false := by
  have hcurrent : currentTape q=false := by
    unfold currentTape
    rw [run_2133586]
    simp [toConfig,cfg,bitSnapshot,show ¬ (q<8) by omega]
  have hpost : postReturn q=false := by
    rw [postReturn_eq]
    simpa [setAt,returnedTape,fillRange,show q≠(-3:Int) by omega,
      show q≠(6:Int) by omega,show q≠(-2:Int) by omega,
      show ¬((0:Int)≤q ∧ q<3) by omega] using hcurrent
  have hshift : shiftedTape q=false := by
    simpa [shiftedTape,afterDispatch,setAt,clearAt,show q≠(7:Int) by omega,
      show q≠(6:Int) by omega,show q≠(-2:Int) by omega] using hpost
  have hafter : afterAllZero q=false := by
    rw [after_bank_frame q (by omega)]
    exact hshift
  have hterminal : terminalTape q=false := by
    simpa [terminalTape,show q≠(-5:Int) by omega,show q≠(5:Int) by omega,
      show q≠(6:Int) by omega,show q≠(7:Int) by omega,show q≠(8:Int) by omega] using hafter
  have hbank : nextBankTape q=false := by
    rw [next_bank_segment.2.1 q (by omega) (Or.inr (by omega))]
    exact hterminal
  have hreturn : returnTape q=false := by
    simpa [returnTape,scanTape,carryTape,result,cleared,put,clearRange,
      show q≠(3:Int) by omega,show q≠(-2:Int) by omega,
      show q≠(-8:Int) by omega,show ¬((-1:Int)≤q ∧ q<4) by omega,
      show ¬((-8:Int)<q ∧ q≤ -5) by omega] using hbank
  simpa [inputTape,clearAt,afterZero,fillRange,setAt,show q≠(-6:Int) by omega,
    show ¬((-4:Int)≤q ∧ q<3) by omega] using hreturn

#print axioms input_right_blank
end Shared.Beeping.NPcoNP.Bootstrap284SecondBlankRay
