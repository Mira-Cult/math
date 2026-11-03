import Shared.PNP.Record285.GenericDispatch

/-! Compose the generic detector, root traversal and forward path into the
existing full-tape path-check interface. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GenericDispatch
open Shared.Beeping.Machines
open Shared.PNP.Record285.SymbolicDispatch

def scanWord (code : List Bool) : List Bool := code.reverse ++ [false,true,true]

def rootLeft : List Bool := [false,true,true]++List.replicate 6 false

theorem scanWord_length (code : List Bool) : (scanWord code).length = code.length+3 := by
  simp [scanWord]

theorem pathStart_leftWord (code : List Bool) :
    pathStart code = leftWord (detectorState 0) (-1) (scanWord code) false
      (List.replicate 5 false) [true,false] := by
  cases hc : code.reverse with
  | nil => simp [pathStart,pathLeft,scanWord,leftWord,hc,detectorState,IncrementPreparation.dispatch0]
  | cons b bs => simp [pathStart,pathLeft,scanWord,leftWord,hc,detectorState,IncrementPreparation.dispatch0]

theorem scanWord_reverse (code : List Bool) :
    (scanWord code).reverse = [true,true,false]++code := by
  simp [scanWord,List.reverse_append]

theorem terminal_target_row (i : Nat) (hi : i < 15) :
    NumericTables.target.table.row (IncrementPreparation.terminal i) true =
      ⟨false,.right,IncrementSelector.literalState (i+2),false⟩ := by
  rw [← ArtifactEndpoint.literal_rows]
  exact (IncrementPreparation.terminal_rows i hi).2

/-- The last dispatcher transition clears the marker and enters the literal
index-specific selector. -/
theorem terminal_last (code : List Bool) (i : Nat) (hi : i < 15) :
    run 1 ⟨IncrementPreparation.terminal i,0,code.reverse++rootLeft,true,[false]⟩ =
      some (pathEnd code i) := by
  simp [run,SymbolicDispatch.step,terminal_target_row i hi,pathEnd,pathLeft,rootLeft]

/-- A safe detector word plus an actual forward literal route implies the
existing verified full redispatch check, uniformly for all finite words. -/
theorem pathCheck_of_safe_route (code : List Bool) (i : Nat) (hi : i < 15)
    (hsafe : detectorRun 0 (scanWord code) = some 0)
    (hroute : route treeRoot code = some (IncrementPreparation.terminal i)) :
    pathCheck code i = true := by
  apply decide_eq_true_eq.mpr
  let len := code.length
  have hs := detector_scan (scanWord code) 0 0 (by decide) hsafe (-1) false
    (List.replicate 5 false) [true,false]
  rw [scanWord_length,scanWord_reverse] at hs
  have hr := reset_root code (-1-(len+3:Nat))
  have hrouteRun := route_scan code treeRoot (IncrementPreparation.terminal i) hroute
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

end Shared.PNP.Record285.GenericDispatch
