import Shared.Beeping.NPcoNP.Source284GraphPrepStep
import Shared.Beeping.NPcoNP.Source284ClockStability

/-! The checked coalesced register graph simulates every step of the bounded
numeric source evaluator. The proof begins from an explicitly supplied PC-50
bank; graph-to-physical tape simulation and the outer search are separate. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphEvaluator
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyRow
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops
open Shared.Beeping.NPcoNP.Source284GraphPrepStep
open Shared.Beeping.NPcoNP.Source284GraphRowStep
open Shared.Beeping.NPcoNP.Source284Relative
abbrev Bank := PASoundness.RegisterMachine.Bank 12

/-- An already accepting source state consumes one clock tick in two silent
graph steps and leaves both half tapes and the source state unchanged. -/
theorem row51_zero (b : Bank) (l r d a w t : Nat) :
    target.system.step ⟨51,regs b l r 0 d a w t⟩ =
      (⟨50,regs b l r 0 d a w t⟩,[]) := by rfl

theorem accepting_tick (b : Bank) (l r d t : Nat) :
    Seg ⟨50,regs b l r 0 d 0 0 (t+1)⟩ ⟨50,regs b l r 0 d 0 0 t⟩ 2 := by
  simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row50,row51_zero]

def tickCost (description : Nat) (c : Source284Relative.Config) : Nat :=
  if c.state=0 then 2 else prepareCost description c.right + stepCost description c

/-- Each source step has a positive finite silent graph segment and consumes
exactly one unit of the supplied source clock. -/
theorem tick (b : Bank) (description remaining : Nat) (c : Source284Relative.Config) :
    0 < tickCost description c ∧
    Seg ⟨50,regs b c.left c.right c.state description 0 0 (remaining+1)⟩
      ⟨50,regs b (Source284Relative.step description c).left
        (Source284Relative.step description c).right
        (Source284Relative.step description c).state description 0 0 remaining⟩
      (tickCost description c) := by
  by_cases hz : c.state=0
  · have he : Source284Relative.step description c = c := step_absorbing description c hz
    simp only [tickCost,hz,if_true,he]
    exact ⟨by decide,by simpa [hz] using accepting_tick b c.left c.right description remaining⟩
  · have hp : 0 < c.state := by omega
    have ht : c.state-1+1=c.state := by omega
    have hprep := prepare b c.left c.right (c.state-1) description remaining
    have hprep' : Seg ⟨50,regs b c.left c.right c.state description 0 0 (remaining+1)⟩
        ⟨60,regs b c.left (c.right/2) (ordinal c) description 0 description remaining⟩
        (prepareCost description c.right) := by
      simpa only [ht,ordinal] using hprep
    have hrow := row_step b description remaining c hz
    refine ⟨?_,?_⟩
    · simp only [tickCost,hz,if_false]
      have hh := hrow.1
      omega
    · simp only [tickCost,hz,if_false]
      exact cat hprep' hrow.2

/-- Exact total graph cost, recursively charging the actual source trajectory.
This is finite for every natural clock; it is not a bit-cost bound. -/
def evalCost (description : Nat) (c : Source284Relative.Config) : Nat → Nat
  | 0 => 0
  | n+1 => tickCost description c + evalCost description (Source284Relative.step description c) n

/-- A finite clock produces exactly the bounded source run. No target step
emits an event anywhere in the complete segment. -/
theorem evaluate (b : Bank) (description : Nat) (c : Source284Relative.Config) (clock : Nat) :
    Seg ⟨50,regs b c.left c.right c.state description 0 0 clock⟩
      ⟨50,regs b (Source284Relative.run description c clock).left
        (Source284Relative.run description c clock).right
        (Source284Relative.run description c clock).state description 0 0 0⟩
      (evalCost description c clock) := by
  induction clock generalizing c with
  | zero => simp [Seg,evalCost,WordEventSystem.advance,WordEventSystem.wordFrom]
  | succ clock ih =>
    have ht := tick b description clock c
    have hi := ih (Source284Relative.step description c)
    have hr : Source284Relative.run description c (clock+1) =
        Source284Relative.run description (Source284Relative.step description c) clock := by
      rw [show clock+1=1+clock by omega,run_add_clock]
      rfl
    rw [evalCost,hr]
    exact cat ht.2 hi

/-- The parsed embedded graph realizes the entire bounded evaluator segment
and its empty event word, for every finite clock. -/
theorem embedded_evaluate (b : Bank) (description : Nat) (c : Source284Relative.Config) (clock : Nat) :
    ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
      (fun g => Grammar284.coreGraph g 53)).bind
      (fun g => GraphExtendedTrace.graphTrace g
        ⟨50,regs b c.left c.right c.state description 0 0 clock⟩ (evalCost description c clock)) =
    some (⟨50,regs b (Source284Relative.run description c clock).left
        (Source284Relative.run description c clock).right
        (Source284Relative.run description c clock).state description 0 0 0⟩,[]) := by
  rw [Grammar284CoreTrace.embeddedGraph_run]
  have h := evaluate b description c clock
  rw [h.1,h.2]

end Shared.Beeping.NPcoNP.Source284GraphEvaluator
