import Shared.PNP.Record285.ControlSafe
import Shared.PNP.Record285.ControlLeaf
import Shared.PNP.Record285.GrammarBeepUnique

/-! Complete one-level grammar continuation from root to root. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ControlContinue
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.IncrementPreparation (break0)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.ControlInvariant

def continueAfterOne : List Bool → Option (List Bool)
  | [] => none
  | true::rest => some (rest.reverse++[true])
  | false::rest => continueAfterOne rest

def continuePathOne (code : List Bool) : Option (List Bool) :=
  continueAfterOne code.reverse.tail

theorem continue_after_one (xs : List Bool) (h : true ∈ xs) :
    continueAfterOne xs = some ((peelZeros xs).2.reverse++[true]) := by
  induction xs with
  | nil => simp at h
  | cons b bs ih =>
    cases b with
    | true => rfl
    | false =>
      have hb : true ∈ bs := by simpa using h
      simpa only [continueAfterOne,peelZeros] using ih hb

theorem continue_one_prior_true (pre : List Bool)
    (hwalk : walk 162 (pre++[true]) = some (.cont 1)) : true ∈ pre.reverse := by
  have ht : true ∈ pre := by
    cases pre with
    | nil => simp [walk,root_true_edge] at hwalk
    | cons b bs =>
      cases b with
      | true => simp
      | false =>
        cases bs <;> simp [walk,root_false_edge] at hwalk
  simpa using ht

theorem continue_path_one (pre : List Bool) (h : true ∈ pre.reverse) :
    continuePathOne (pre++[true]) = some ((peelZeros pre.reverse).2.reverse++[true]) := by
  simpa [continuePathOne,List.reverse_append] using continue_after_one pre.reverse h

/-- The `continue.1` leaf takes a positive silent root-to-root run and
preserves both full tape tails. -/
theorem root_continue_one (code : List Bool) (hwalk : walk 162 code = some (.cont 1))
    (head : Int) (leftTail rightTail : Nat) :
    ∃ pre, code = pre++[true] ∧
      let p := peelZeros pre.reverse
      let precode := p.2.reverse
      let steps := code.length+p.1+1+(precode.length+17)
      continuePathOne code = some (precode++[true]) ∧
      silent Record285.machine steps (rootEntry code head leftTail rightTail) =
        some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
          (head-2-p.1) leftTail (2*pushBit p.1 false rightTail)) ∧ 0 < steps := by
  obtain ⟨pre,parent,row,hcode,_,_,_,_,hsafe⟩ := continue_prefix_safe code 1 hwalk
  have hprior : true ∈ pre.reverse := continue_one_prior_true pre (by simpa [hcode] using hwalk)
  have hf := literal_control_leaf code pre (.cont 1) break0
    (by simpa only [rootIndex] using hwalk) hcode (by decide) (by decide) head leftTail rightTail
  have hr := continue_one_return pre hprior hsafe (head-2) leftTail rightTail
  refine ⟨pre,hcode,?_,?_,by omega⟩
  · rw [hcode]
    exact continue_path_one pre hprior
  · rw [show code.length+(peelZeros pre.reverse).1+1+
        ((peelZeros pre.reverse).2.reverse.length+17) =
        code.length+((peelZeros pre.reverse).1+1+((peelZeros pre.reverse).2.reverse.length+17)) by omega,
      silent_add,hf]
    simp only [Option.bind_some]
    exact hr

theorem root_continue_one_physical (code : List Bool) (hwalk : walk 162 code = some (.cont 1))
    (head : Int) (leftTail rightTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail rightTail) physical) :
    ∃ pre, code = pre++[true] ∧
      let p := peelZeros pre.reverse
      let precode := p.2.reverse
      let steps := code.length+p.1+1+(precode.length+17)
      continuePathOne code = some (precode++[true]) ∧
      Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-2-p.1) leftTail (2*pushBit p.1 false rightTail))
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
      0 < steps := by
  obtain ⟨pre,hcode,hpath,hs,hpos⟩ := root_continue_one code hwalk head leftTail rightTail
  have hp := silent_physical Record285.machine _ physical hrel _ _ hs
  exact ⟨pre,hcode,hpath,hp.1,hp.2,hpos⟩

/-- The following bit may be either value; the entire suffix is preserved. -/
theorem root_continue_one_any (code : List Bool) (hwalk : walk 162 code = some (.cont 1))
    (marker : Bool) (head : Int) (leftTail rightTail : Nat) :
    ∃ pre, code = pre++[true] ∧
      let p := peelZeros pre.reverse
      let precode := p.2.reverse
      let steps := code.length+p.1+1+(precode.length+17)
      continuePathOne code = some (precode++[true]) ∧
      silent Record285.machine steps
        (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail) =
        some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
          (head-2-p.1) leftTail (pushBit p.1 false (RelativeTape.bitVal marker+2*rightTail))) ∧ 0 < steps := by
  obtain ⟨pre,parent,row,hcode,_,_,_,_,hsafe⟩ := continue_prefix_safe code 1 hwalk
  have hprior : true ∈ pre.reverse := continue_one_prior_true pre (by simpa [hcode] using hwalk)
  have hf := literal_control_leaf_any code pre (.cont 1) break0
    (by simpa only [rootIndex] using hwalk) hcode (by decide) (by decide) marker head leftTail rightTail
  have hr := continue_one_return_any pre hprior hsafe (head-2) leftTail (RelativeTape.bitVal marker+2*rightTail)
  refine ⟨pre,hcode,?_,?_,by omega⟩
  · rw [hcode]
    exact continue_path_one pre hprior
  · rw [show code.length+(peelZeros pre.reverse).1+1+
        ((peelZeros pre.reverse).2.reverse.length+17) =
        code.length+((peelZeros pre.reverse).1+1+((peelZeros pre.reverse).2.reverse.length+17)) by omega,
      silent_add,hf]
    simp only [Option.bind_some]
    exact hr

theorem root_continue_one_any_physical (code : List Bool) (hwalk : walk 162 code = some (.cont 1))
    (marker : Bool) (head : Int) (leftTail rightTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail)
      physical) :
    ∃ pre, code = pre++[true] ∧
      let p := peelZeros pre.reverse
      let precode := p.2.reverse
      let steps := code.length+p.1+1+(precode.length+17)
      continuePathOne code = some (precode++[true]) ∧
      Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-2-p.1) leftTail (pushBit p.1 false (RelativeTape.bitVal marker+2*rightTail)))
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
      0 < steps := by
  obtain ⟨pre,hcode,hpath,hs,hpos⟩ := root_continue_one_any code hwalk marker head leftTail rightTail
  have hp := silent_physical Record285.machine _ physical hrel _ _ hs
  exact ⟨pre,hcode,hpath,hp.1,hp.2,hpos⟩

end Shared.PNP.Record285.ControlContinue
