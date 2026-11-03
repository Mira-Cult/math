import Shared.PNP.Record285.GrammarHalfRoute
import Shared.PNP.Record285.HalfPreparation
import Shared.PNP.Record285.DecrementSelector

/-! Complete clean-terminal preparation and redispatch for every half
grammar path. The selected field operation remains a separate obligation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.HalfDispatch
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar

def pathEnd (code : List Bool) (i : Nat) : SymbolicDispatch.Config :=
  ⟨HalfPreparation.selector i,1,false::pathLeft code,false,[]⟩

theorem terminal_last (code : List Bool) (i : Nat) (hi : i < 4) :
    run 1 ⟨halfTerminal i,0,code.reverse++rootLeft,true,[false]⟩ =
      some (pathEnd code i) := by
  have hr := (HalfPreparation.terminal_rows i hi).2
  rw [ArtifactEndpoint.literal_rows] at hr
  simp [run,SymbolicDispatch.step,hr,pathEnd,pathLeft,rootLeft]

/-- The actual literal detector and root scan redispatch every grammar
half word to its field-specific selector on the complete tape. -/
theorem symbolic_redispatch (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.half i)) :
    run (pathCost code) (pathStart code) = some (pathEnd code i) := by
  obtain ⟨hi,hroute,hsafe⟩ := producer_half_safe code i hwalk
  let len := code.length
  have hs := detector_scan (scanWord code) 0 0 (by decide) hsafe (-1) false
    (List.replicate 5 false) [true,false]
  rw [scanWord_length,scanWord_reverse] at hs
  have hr := reset_root code (-1-(len+3:Nat))
  have hrouteRun := route_scan code treeRoot (halfTerminal i) hroute
    (-(len:Int)) true rootLeft [false]
  have hlast := terminal_last code i hi
  unfold pathCost
  rw [show 2*code.length+18 = (code.length+3)+(14+(code.length+1)) by omega,
    run_add,pathStart_leftWord,hs]
  simp only [Option.bind_some]
  rw [run_add]
  have hr' : run 14
      ⟨detectorState 0,-1-(len+3:Nat),List.replicate 5 false,false,
        [true,true,false]++code++[true,false]⟩ =
      some (rightWord treeRoot (-(len:Int)) code true rootLeft [false]) := by
    have hp : (-1:Int)-(len+3:Nat)+4 = -(len:Int) := by omega
    simpa only [hp,rootLeft] using hr
  rw [hr']
  simp only [Option.bind_some]
  rw [run_add,hrouteRun]
  simp only [Option.bind_some]
  have hp : -(len:Int)+(code.length:Int) = 0 := by dsimp [len]; omega
  simp only [hp] at hlast ⊢
  exact hlast

theorem literal_redispatch (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.half i)) (origin : Int) (leftTail rightTail : Nat) :
    silent Record285.machine (pathCost code)
      (atLeftWord IncrementPreparation.dispatch0 (origin-1)
        (bits (pathLeft code) leftTail) (1+4*rightTail)) =
      some ⟨HalfPreparation.selector i,origin+1,2*bits (pathLeft code) leftTail,
        false,rightTail⟩ := by
  have h := run_sound (pathCost code) (pathStart code) (pathEnd code i)
    (symbolic_redispatch code i hwalk) origin leftTail rightTail
  rw [path_start_denote] at h
  simpa only [pathEnd,denote,bits,Shared.PNP.Record285.RelativeTape.bitVal,
    Bool.false_eq_true,if_false,Nat.zero_add] using h

/-- Preparation and redispatch together are a finite silent segment from
the clean literal half terminal to the field-specific selector. -/
theorem terminal_to_selector (code : List Bool) (i gap : Nat)
    (hwalk : walk 162 code = some (.half i)) (head : Int) (leftTail tail : Nat) :
    silent Record285.machine ((2*gap+5)+pathCost code)
      ⟨halfTerminal i,head,bits (pathLeft code) leftTail,false,
        2*runPattern false gap true tail⟩ =
      some ⟨HalfPreparation.selector i,head+1,2*bits (pathLeft code) leftTail,
        false,pushBit (gap+1) true tail⟩ := by
  obtain ⟨hi,_,_⟩ := producer_half_safe code i hwalk
  have hp := HalfPreparation.literal_prepare i hi gap head (bits (pathLeft code) leftTail) tail
  have hr := literal_redispatch code i hwalk head leftTail (pushBit (gap+1) true tail)
  rw [silent_add,hp]
  simpa only [Option.bind_some] using hr

theorem terminal_to_selector_physical (code : List Bool) (i gap : Nat)
    (hwalk : walk 162 code = some (.half i)) (head : Int) (leftTail tail : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨halfTerminal i,head,bits (pathLeft code) leftTail,false,
      2*runPattern false gap true tail⟩ physical) :
    Rel ⟨HalfPreparation.selector i,head+1,2*bits (pathLeft code) leftTail,
      false,pushBit (gap+1) true tail⟩
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run ((2*gap+5)+pathCost code)) ∧
    (∀ t, t < (2*gap+5)+pathCost code →
      ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < (2*gap+5)+pathCost code := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (terminal_to_selector code i gap hwalk head leftTail tail)
  exact ⟨hp.1,hp.2,by omega⟩


end Shared.PNP.Record285.HalfDispatch
