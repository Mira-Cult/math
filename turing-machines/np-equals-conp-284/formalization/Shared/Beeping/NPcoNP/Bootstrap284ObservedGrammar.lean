import Shared.Beeping.NPcoNP.Bootstrap284ControlSelector
import Shared.Beeping.NPcoNP.Bootstrap284SimulationProgress
import Shared.Beeping.NPcoNP.Grammar284Numbering
import Shared.Beeping.NPcoNP.GrammarFullRowsCoverage
/-! The observed syntactic leaf is administrative, and its occurrence is
inside any supplied first source-step simulation. No simulation is asserted. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284ObservedGrammar

open PASoundness Shared.Beeping
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284BulkContinue7665
open Shared.Beeping.NPcoNP.Bootstrap284State97
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
open Shared.Beeping.NPcoNP.Bootstrap284ControlSelector
open Shared.Beeping.NPcoNP.Bootstrap284SimulationEndpoint
open Shared.Beeping.NPcoNP.Bootstrap284SimulationProgress
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.GrammarFullRowsCoverage
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

theorem observed_leaf_index :
    traceState557.acc.leaves[2]? = some (observedPath,"_continue.1") := by decide

theorem observed_tag : operationTag "_continue.1" = some (.continue 1) := by decide

theorem observed_full_row :
    fullRow traceState557.acc.starts (observedPath,"_continue.1") = some ⟨"jump",[1]⟩ := by
  have hleaf : 2<traceState557.acc.leaves.size := by rw [producerLeafCount]; decide
  have hc := allRows 2 hleaf
  have hr : producerFullRows[2]? = some ⟨"jump",[1]⟩ := by decide
  simp only [indexedRowCheck,observed_leaf_index,hr,beq_iff_eq] at hc
  exact hc

theorem observed_not_retained : producerNumbering.map[2]? = some none := by decide

theorem observed_contracted_target :
    Shared.Beeping.NPcoNP.Grammar284.target producerFullRows producerNumbering.map (producerFullRows.size+1) 2 = some 1 := by decide

/-- The contracted destination is the first conditional decrement of
coalesced register 4. This identifies graph data, not the physical PC. -/
theorem contracted_pc1_instruction :
    let ins := Shared.Beeping.NPcoNP.Parent290Coalesced.target.code[1]
    ins.action = .base (.decNZ 4) ∧ ins.yes=1 ∧ ins.no=2 := by
  exact ⟨rfl,rfl,rfl⟩

theorem graph_initial_state :
    (Shared.Beeping.NPcoNP.Parent290Coalesced.target.system.initial.state : Fin 185)=0 := by decide

theorem post_boot_132_silent :
    physical.wordFrom (toConfig (-4096) 4104 output7665) 132 = [] := by
  change (machineWordSystem machine (BitLabels.fromFlags machine)).wordFrom
    (toConfig (-4096) 4104 output7665) 132 = []
  rw [← ScalarWordRefinement.beepBits_machine]
  change ((WordEventSystem.ofBeep machine.system).map (fun _ => true)).wordFrom
    (toConfig (-4096) 4104 output7665) 132 = []
  rw [WordEventSystem.map_wordFrom]
  have hp : silentSegment machine (toConfig (-4096) 4104 output7665)
      (toConfig (-4096) 4104 after66) 94 := by
    simpa using segAdd machine _ _ _ 28 66 segment28 segment66
  have ht : silentSegment machine (toConfig (-4096) 4104 after66)
      (cfg 93 (-28) returnedTape) 38 := by
    rw [← run_2133586]
    exact second_return_segment
  have h := segAdd machine _ _ _ 94 38 hp ht
  have hunit : (WordEventSystem.ofBeep machine.system).wordFrom
      (toConfig (-4096) 4104 output7665) 132 = [] := by
    simpa only [W] using h.2
  rw [hunit]
  rfl

theorem first_duration_gt_132 (r : PostBootstrapSimulation) :
    132 < r.duration Shared.Beeping.NPcoNP.Parent290Coalesced.target.system.initial (toConfig (-4096) 4104 output7665) :=
  first_duration_gt_of_silent r 132 post_boot_132_silent

/-- The observed visit occurs 101 steps after bootstrap and must lie
strictly inside the first source macrostep of any valid certificate. -/
theorem observed_before_first_step_finishes (r : PostBootstrapSimulation) :
    101 < r.duration Shared.Beeping.NPcoNP.Parent290Coalesced.target.system.initial
      (toConfig (-4096) 4104 output7665) := by
  have h := first_duration_gt_132 r
  omega

#print axioms observed_before_first_step_finishes
#print axioms contracted_pc1_instruction
#print axioms observed_full_row
#print axioms observed_contracted_target
#print axioms first_duration_gt_132

end Shared.Beeping.NPcoNP.Bootstrap284ObservedGrammar
