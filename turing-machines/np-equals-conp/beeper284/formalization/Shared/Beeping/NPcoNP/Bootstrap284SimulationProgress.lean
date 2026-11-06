import Shared.Beeping.NPcoNP.Bootstrap284SimulationEndpoint
import Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch

/-! Concrete consequences of the required first source event. A claimed
simulation duration cannot end inside any proved silent physical prefix.
No bound here is a substitute for the eventual-silence equivalence. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284SimulationProgress

open PASoundness Shared.Beeping
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284BulkContinue7665
open Shared.Beeping.NPcoNP.Bootstrap284State97
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284SimulationEndpoint

/-- Any source-step simulation ending with the first beep must extend
beyond an independently established silent physical prefix. -/
theorem first_duration_gt_of_silent (r : PostBootstrapSimulation) (k : Nat)
    (hquiet : physical.wordFrom (toConfig (-4096) 4104 output7665) k = []) :
    k < r.duration target.system.initial (toConfig (-4096) 4104 output7665) := by
  let n := r.duration target.system.initial (toConfig (-4096) 4104 output7665)
  by_contra hn
  have hle : n ≤ k := by omega
  have hprefix : physical.wordFrom (toConfig (-4096) 4104 output7665) n = [] := by
    have hh : physical.wordFrom (toConfig (-4096) 4104 output7665) n ++
        physical.wordFrom (physical.advance (toConfig (-4096) 4104 output7665) n) (k-n) = [] := by
      rw [← WordEventSystem.wordFrom_add]
      simpa [Nat.add_sub_of_le hle] using hquiet
    exact (List.append_eq_nil_iff.mp hh).1
  have hevent := r.word_eq target.system.initial (toConfig (-4096) 4104 output7665) r.initial
  rw [source_initial_word] at hevent
  change physical.wordFrom (toConfig (-4096) 4104 output7665) n = [true] at hevent
  rw [hprefix] at hevent
  contradiction

/-- The exact two checked post-bootstrap blocks give 94 silent transitions. -/
theorem post_boot_94_silent :
    physical.wordFrom (toConfig (-4096) 4104 output7665) 94 = [] := by
  change (machineWordSystem machine (BitLabels.fromFlags machine)).wordFrom
    (toConfig (-4096) 4104 output7665) 94 = []
  rw [← ScalarWordRefinement.beepBits_machine]
  change ((WordEventSystem.ofBeep machine.system).map (fun _ => true)).wordFrom
    (toConfig (-4096) 4104 output7665) 94 = []
  rw [WordEventSystem.map_wordFrom]
  have h := segAdd machine _ _ _ 28 66 segment28 segment66
  have hunit : (WordEventSystem.ofBeep machine.system).wordFrom
      (toConfig (-4096) 4104 output7665) 94 = [] := by
    simpa only [W] using h.2
  rw [hunit]
  rfl

theorem first_duration_gt_94 (r : PostBootstrapSimulation) :
    94 < r.duration target.system.initial (toConfig (-4096) 4104 output7665) :=
  first_duration_gt_of_silent r 94 post_boot_94_silent

end Shared.Beeping.NPcoNP.Bootstrap284SimulationProgress

#print axioms Shared.Beeping.NPcoNP.Bootstrap284SimulationProgress.first_duration_gt_94
