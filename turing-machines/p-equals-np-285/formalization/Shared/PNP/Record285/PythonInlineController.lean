import Shared.PNP.Record285.PythonInlineDecoder
import Shared.PNP.Record285.AlignedPhysicalEvents

/-! A manually transcribed source controller using the Python-style inline
bounded evaluator. Its equality with the physical-refinement source does not
establish a parsing theorem for `selected_source.py`. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonInlineController
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.AlignedPhysical

/-- Explicit inline reference-versus-candidate mismatch. -/
def compare (s : SearchState) : Bool :=
  PythonInlineDecoder.search (s.radix+s.remaining) s.n s.radix !=
    PythonInlineDecoder.halted s.program ((s.n+2)^s.exponent)
      ⟨0,(frame s.radix s.remaining)/2,2*((frame s.radix s.remaining)%2),0⟩

/-- A complete Python-style event/reset or comparison/schedule action.
The controller is finite between these action boundaries. -/
def step (s : SearchState) : SearchState × Bool :=
  match s.phase with
  | .begin => (⟨s.program,s.exponent,0,1,0,.compare⟩,true)
  | .compare =>
      if compare s then
        if s.program = 0 then
          (⟨s.exponent,1,s.n,s.radix,s.remaining,.begin⟩,false)
        else (⟨s.program-1,s.exponent+1,s.n,s.radix,s.remaining,.begin⟩,false)
      else if s.remaining=0 then
        (⟨s.program,s.exponent,s.n+1,2*s.radix,2*s.radix-1,.compare⟩,false)
      else (⟨s.program,s.exponent,s.n,s.radix,s.remaining-1,.compare⟩,false)

theorem compare_eq (s : SearchState) :
    compare s = mismatch s.program s.exponent s.n s.radix s.remaining :=
  PythonInlineDecoder.comparison_correct _ _ _ _ _

theorem step_eq (s : SearchState) : step s = controllerStep s := by
  cases hp : s.phase with
  | begin => simp [step,controllerStep,hp]
  | compare =>
    simp only [step,controllerStep,hp,compare_eq]
    split
    · simp only [advanceCandidate]
      split <;> rfl
    · rfl

def controller : EventSystem SearchState :=
  ⟨⟨0,1,0,1,0,.begin⟩,step⟩

theorem controller_eq : controller = Shared.PNP.Record285.Source.controller := by
  unfold controller Shared.PNP.Record285.Source.controller
  congr 1
  funext s
  exact step_eq s

/-- Every reachable model state has positive radix, so the actual source's
subtraction by one is nonnegative on all such comparison inputs. -/
theorem reachable_radix_positive (t : Nat) : 0 < (controller.run t).radix := by
  rw [controller_eq]
  have h := Shared.PNP.Record285.Source.controller_inputInvariant t
  have hp : 0 < 2^(Shared.PNP.Record285.Source.controller.run t).n := Nat.pow_pos (by decide)
  rw [h.1]
  exact hp

theorem reachable_frame_subtraction_safe (t : Nat) :
    0 < 2*((controller.run t).remaining*(controller.run t).radix) +
      (controller.run t).radix := by
  have hp := reachable_radix_positive t
  omega

/-- Every action of the transcribed controller is realized by a positive,
finite physical segment between configurations related on the entire tape,
with exact marked-event accounting. -/
theorem physical_action (i : Nat) :
    Rel (controller.run i) (Shared.PNP.Record285.machine.system.run (boundary i)) ∧
    boundary i < boundary (i+1) ∧
    Rel (controller.run (i+1))
      (Shared.PNP.Record285.machine.system.advance
        (Shared.PNP.Record285.machine.system.run (boundary i)) (boundary (i+1)-boundary i)) ∧
    (controller.BeepAt i ↔
      Shared.PNP.Record285.machine.system.HasEvent (boundary i) (boundary (i+1))) ∧
    Shared.PNP.Record285.machine.system.UniqueEvents (boundary i) (boundary (i+1)) := by
  rw [controller_eq]
  exact source_action_physical_segment i

end Shared.PNP.Record285.PythonInlineController
