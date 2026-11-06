import Shared.Beeping.NPcoNP.NativeUnit261Cycle83
import Shared.Beeping.NPcoNP.Bootstrap284Unit261Return

/-! The supplied-layout return to state 83 has a verified blank-start seed. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284Unit261Actual83
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeUnitCarry83
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
open Shared.Beeping.NPcoNP.Bootstrap284Unit261Return
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

def postIncrement : Int → Bool := setAt 6 (clearAt (-2) returnedTape)
def carry4Tape (t : Int → Bool) : Int → Bool :=
  let u := put (put t (-3) true) 0 false
  put (clearRange u 1 4) 3 true

def postCarry : Int → Bool := carry4Tape postIncrement

/-- Numeric specialization is proved before substituting the large tape. -/
theorem carry4 (t : Int → Bool) (hpre : t (-3)=false) (h0 : t (-2)=false)
    (h1 : t (-1)=false) (run : Holds t 0 (List.replicate 4 true ++ [false])) :
    ∃ n : Nat, 0<n ∧ silentSegment machine (cfg 1 (-3) t) (cfg 83 (-4) (carry4Tape t)) n := by
  have hpre' : t ((-2 : Int)-1)=false := by simpa only [Int.reduceSub] using hpre
  have h1' : t ((-2 : Int)+1)=false := by simpa only [Int.reduceAdd] using h1
  have hrun' : Holds t ((-2 : Int)+2) (List.replicate 4 true ++ [false]) := by
    simpa only [Int.reduceAdd] using run
  obtain ⟨n,hn,hseg⟩ := carry_to83 4 (-2) t (by decide) hpre' h0 h1' hrun'
  refine ⟨n,hn,?_⟩
  simpa only [carry4Tape,Nat.cast_ofNat,Int.reduceAdd,Int.reduceSub,Int.reduceNeg] using hseg

theorem postIncrement_pre : postIncrement (-3)=false := by
  unfold postIncrement returnedTape currentTape
  rw [run_2133586]
  decide

theorem postIncrement_h0 : postIncrement (-2)=false := by simp [postIncrement,setAt,clearAt]

theorem postIncrement_h1 : postIncrement (-1)=false := by
  unfold postIncrement returnedTape currentTape
  rw [run_2133586]
  decide

theorem postIncrement_scan : Holds postIncrement 0 (List.replicate 4 true ++ [false]) := by
  unfold postIncrement returnedTape currentTape
  rw [run_2133586]
  simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds]
  all_goals decide

/-- A further positive finite silent continuation is obtained by the
parameterized carry theorem, starting from the proved blank-start run. -/
theorem blank_start_unit_to83 : ∃ n : Nat, 0<n ∧
    silentSegment machine (machine.system.run 0) (cfg 83 (-4) postCarry) (2133669+n) := by
  obtain ⟨n,hn,hseg⟩ := carry4 postIncrement postIncrement_pre postIncrement_h0
    postIncrement_h1 postIncrement_scan
  refine ⟨n,hn,?_⟩
  have hstart : silentSegment machine (machine.system.run 0) (cfg 1 (-3) postIncrement) 2133669 :=
    blank_start_unit_return1
  exact segAdd machine _ _ _ 2133669 n hstart hseg

#print axioms blank_start_unit_to83
end Shared.Beeping.NPcoNP.Bootstrap284Unit261Actual83
