import Shared.Beeping.NPcoNP.Source284TableSimulationEndpoint
import Shared.Beeping.NPcoNP.Bootstrap284BankPrefix

/-! Reduce the selected-table binding to a post-bootstrap operational
simulation. The startup length, final configuration and empty event word
are proved for the literal table. The post-bootstrap relation and positive,
event-preserving step simulations remain explicit obligations. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284SimulationEndpoint

open ComplexityTheory PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284BulkContinue7665
open Shared.Beeping.NPcoNP.Bootstrap284FirstExit
open Shared.Beeping.NPcoNP.Source284GraphTableConditional
open Shared.Beeping.NPcoNP.Source284TableSimulationEndpoint

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

abbrev GraphConfig := RegisterMachine.Config 12 185
abbrev TapeConfig := Config 284
abbrev physical := machineWordSystem machine (BitLabels.fromFlags machine)

/-- The remaining proof obligations start at the checked physical snapshot.
The relation is not supplied by this interface and must establish the real
register/tape interpretation for every reachable source macrostep. -/
structure PostBootstrapSimulation where
  Rel : GraphConfig → TapeConfig → Prop
  initial : Rel target.system.initial (toConfig (-4096) 4104 output7665)
  duration : GraphConfig → TapeConfig → Nat
  positive : ∀ s t, Rel s t → 0 < duration s t
  next : ∀ s t, Rel s t →
    Rel (target.system.step s).1 (physical.advance t (duration s t))
  word_eq : ∀ s t, Rel s t →
    physical.wordFrom t (duration s t) = (target.system.step s).2

/-- The very first source macrostep emits one beep. A valid physical
certificate must therefore make finite progress to that event. -/
theorem source_initial_word : (target.system.step target.system.initial).2 = [true] := by
  decide

theorem certificate_first_event (r : PostBootstrapSimulation) :
    ∃ n : Nat, 0<n ∧
      physical.wordFrom (toConfig (-4096) 4104 output7665) n = [true] := by
  refine ⟨r.duration target.system.initial (toConfig (-4096) 4104 output7665),
    r.positive _ _ r.initial, ?_⟩
  rw [r.word_eq _ _ r.initial,source_initial_word]

theorem startup_word_silent : physical.prefixWord 2133492 = [] := by
  change (machineWordSystem machine (BitLabels.fromFlags machine)).prefixWord 2133492 = []
  rw [← ScalarWordRefinement.beepBits_machine]
  change ((WordEventSystem.ofBeep machine.system).map (fun _ => true)).prefixWord 2133492 = []
  rw [WordEventSystem.map_prefix]
  have h : (WordEventSystem.ofBeep machine.system).prefixWord 2133492 = [] := by
    change (W machine).wordFrom (machine.system.run 0) 2133492 = []
    exact blank_start_7665.2
  rw [h]
  rfl

/-- Attach the already-checked startup to a post-bootstrap certificate. -/
def bind (r : PostBootstrapSimulation) : GraphTableSimulation machine where
  Rel := r.Rel
  startup := 2133492
  initial := by
    change r.Rel target.system.initial (physical.run 2133492)
    rw [machineWordSystem_run,run_first_exit]
    exact r.initial
  startup_silent := startup_word_silent
  duration := r.duration
  positive := r.positive
  next := r.next
  word_eq := r.word_eq

theorem selected_table_silent_iff_classes (r : PostBootstrapSimulation) :
    machine.system.EventuallySilent ↔ NP = coNP :=
  Source284TableSimulationEndpoint.selected_table_silent_iff_classes (bind r)

end Shared.Beeping.NPcoNP.Bootstrap284SimulationEndpoint

#print axioms Shared.Beeping.NPcoNP.Bootstrap284SimulationEndpoint.startup_word_silent
#print axioms Shared.Beeping.NPcoNP.Bootstrap284SimulationEndpoint.certificate_first_event
#print axioms Shared.Beeping.NPcoNP.Bootstrap284SimulationEndpoint.selected_table_silent_iff_classes
