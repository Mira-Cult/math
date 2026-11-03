import Shared.PNP.Record285.ControlBreakCore
import Shared.PNP.Record285.ControlSafe
import Shared.PNP.Record285.ControlLeaf
import Shared.PNP.Record285.GrammarBeepUnique

/-! Complete literal `break.0` root-to-root control transfer. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ControlBreak
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementCleanup (peel lexical)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.ControlInvariant
open Shared.PNP.Record285.ControlContinue (literal_control_leaf_any)

theorem break_prior_zero (pre : List Bool) (i : Nat)
    (hwalk : walk 162 (pre++[true]) = some (.brk i)) : false ∈ pre.reverse := by
  have hz : false ∈ pre := by
    cases pre with
    | nil => simp [walk,root_true_edge] at hwalk
    | cons a as =>
      cases a with
      | false => simp
      | true =>
        cases as with
        | nil => simp [walk,root_true_edge,next_true_edge] at hwalk
        | cons b bs =>
          cases b with
          | false => simp
          | true => cases bs <;> simp [walk,root_true_edge,next_true_edge] at hwalk
  simpa using hz

/-- A level-zero break from a control root restores the root, with the
precise skip-zero path and full bank. The anchor layout is explicit. -/
theorem root_break_zero (code : List Bool) (hwalk : walk 162 code = some (.brk 0))
    (marker : Bool) (gap : Nat) (head : Int) (leftTail rightTail bank : Nat)
    (hanchor : bitVal marker+2*rightTail = runPattern false gap true (2*bank)) :
    ∃ pre, code = pre++[true] ∧
      let p := peel pre.reverse
      let precode := p.2.reverse
      let steps := code.length+(3*p.1+2*(gap+1)+5)+(precode.length+17)
      returnPath code = some (precode++[true]) ∧
      silent Record285.machine steps
        (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail) =
        some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
          (head-2-p.1) leftTail (runPattern false (p.1+gap) true (2*bank))) ∧ 0 < steps := by
  obtain ⟨pre,parent,row,hcode,_,_,_,_,hsafe⟩ := break_prefix_safe code 0 hwalk
  have hprior := break_prior_zero pre 0 (by simpa [hcode] using hwalk)
  have hf := literal_control_leaf_any code pre (.brk 0) lexical
    (by simpa only [rootIndex] using hwalk) hcode (by decide) (by decide) marker head leftTail rightTail
  rw [hanchor] at hf
  have hr := break_zero_return pre hprior hsafe gap (head-2) leftTail bank
  have hp := return_after_zero pre.reverse hprior
  refine ⟨pre,hcode,?_,?_,by omega⟩
  · simpa [returnPath,hcode,List.reverse_append,returnAfterZero] using hp
  · rw [show code.length+(3*(peel pre.reverse).1+2*(gap+1)+5)+
        ((peel pre.reverse).2.reverse.length+17) =
        code.length+((3*(peel pre.reverse).1+2*(gap+1)+5)+
          ((peel pre.reverse).2.reverse.length+17)) by omega,silent_add,hf]
    simp only [Option.bind_some]
    exact hr

theorem root_break_zero_physical (code : List Bool) (hwalk : walk 162 code = some (.brk 0))
    (marker : Bool) (gap : Nat) (head : Int) (leftTail rightTail bank : Nat)
    (hanchor : bitVal marker+2*rightTail = runPattern false gap true (2*bank))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail)
      physical) :
    ∃ pre, code = pre++[true] ∧
      let p := peel pre.reverse
      let precode := p.2.reverse
      let steps := code.length+(3*p.1+2*(gap+1)+5)+(precode.length+17)
      returnPath code = some (precode++[true]) ∧
      Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-2-p.1) leftTail (runPattern false (p.1+gap) true (2*bank)))
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
      0 < steps := by
  obtain ⟨pre,hcode,hpath,hs,hpos⟩ := root_break_zero code hwalk marker gap head leftTail rightTail bank hanchor
  have hp := silent_physical Record285.machine _ physical hrel _ _ hs
  exact ⟨pre,hcode,hpath,hp.1,hp.2,hpos⟩

end Shared.PNP.Record285.ControlBreak
