import Shared.PNP.Record285.SymbolicDispatchCheck

/-! Kernel-checked literal redispatch paths for the fifteen increment indices. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SymbolicDispatch
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.BootstrapSweep

/-- Each finite certificate checks all read/write/move/flag effects, with
unknown tape tails left untouched by the symbolic checker. -/
theorem dispatch_check (i : Nat) (hi : i < 15) :
    run (dispatchCost i) (dispatchStart i) = some (dispatchEnd i) := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact of_decide_eq_true check0
  · exact of_decide_eq_true check1
  · exact of_decide_eq_true check2
  · exact of_decide_eq_true check3
  · exact of_decide_eq_true check4
  · exact of_decide_eq_true check5
  · exact of_decide_eq_true check6
  · exact of_decide_eq_true check7
  · exact of_decide_eq_true check8
  · exact of_decide_eq_true check9
  · exact of_decide_eq_true check10
  · exact of_decide_eq_true check11
  · exact of_decide_eq_true check12
  · exact of_decide_eq_true check13
  · exact of_decide_eq_true check14


theorem controlLeft_ne_nil (i : Nat) : controlLeft i ≠ [] := by
  simp [controlLeft]

theorem start_denote (i : Nat) (origin : Int) (leftTail rightTail : Nat) :
    denote (dispatchStart i) origin leftTail rightTail =
      IncrementReturn.atLeftWord IncrementPreparation.dispatch0 (origin-1)
        (bits (controlLeft i) leftTail) (1+4*rightTail) := by
  have h := controlLeft_ne_nil i
  cases hc : controlLeft i with
  | nil => exact False.elim (h hc)
  | cons b bs =>
    simp only [dispatchStart,hc,List.tail_cons,List.headD_cons,denote,
      IncrementReturn.atLeftWord,bits_read,bits_drop]
    have hh : origin + (-1) = origin-1 := by omega
    have hr : bits [true,false] rightTail = 1+4*rightTail := by simp [bits,bitVal]; omega
    simp only [hh,hr]

theorem end_denote (i : Nat) (origin : Int) (leftTail rightTail : Nat) :
    denote (dispatchEnd i) origin leftTail rightTail =
      ⟨IncrementSelector.literalState (i+2),origin+1,2*bits (controlLeft i) leftTail,false,rightTail⟩ := by
  simp [denote,dispatchEnd,bits,bitVal]

theorem literal_redispatch (i : Nat) (hi : i < 15) (origin : Int) (leftTail rightTail : Nat) :
    silent Record285.machine (dispatchCost i)
      (IncrementReturn.atLeftWord IncrementPreparation.dispatch0 (origin-1)
        (bits (controlLeft i) leftTail) (1+4*rightTail)) =
      some ⟨IncrementSelector.literalState (i+2),origin+1,2*bits (controlLeft i) leftTail,
        false,rightTail⟩ := by
  have h := run_sound (dispatchCost i) (dispatchStart i) (dispatchEnd i)
    (dispatch_check i hi) origin leftTail rightTail
  simpa only [start_denote,end_denote] using h

/-- The same checker accepts arbitrary control words, not only the fifteen
frozen examples above. The check remains an explicit hypothesis until a word
is certified against the literal table. -/
def pathLeft (code : List Bool) : List Bool :=
  code.reverse ++ [false,true,true] ++ List.replicate 6 false

def pathStart (code : List Bool) : Config :=
  ⟨IncrementPreparation.dispatch0,-1,(pathLeft code).tail,
    (pathLeft code).headD false,[true,false]⟩

def pathEnd (code : List Bool) (i : Nat) : Config :=
  ⟨IncrementSelector.literalState (i+2),1,false::pathLeft code,false,[]⟩

def pathCost (code : List Bool) : Nat := 2*code.length+18

def pathCheck (code : List Bool) (i : Nat) : Bool :=
  decide (run (pathCost code) (pathStart code) = some (pathEnd code i))

theorem pathLeft_ne_nil (code : List Bool) : pathLeft code ≠ [] := by
  simp [pathLeft]

theorem path_start_denote (code : List Bool) (origin : Int) (leftTail rightTail : Nat) :
    denote (pathStart code) origin leftTail rightTail =
      IncrementReturn.atLeftWord IncrementPreparation.dispatch0 (origin-1)
        (bits (pathLeft code) leftTail) (1+4*rightTail) := by
  have h := pathLeft_ne_nil code
  cases hc : pathLeft code with
  | nil => exact False.elim (h hc)
  | cons b bs =>
    simp only [pathStart,hc,List.tail_cons,List.headD_cons,denote,
      IncrementReturn.atLeftWord,bits_read,bits_drop]
    have hh : origin + (-1) = origin-1 := by omega
    have hr : bits [true,false] rightTail = 1+4*rightTail := by simp [bits,bitVal]; omega
    simp only [hh,hr]

theorem path_end_denote (code : List Bool) (i : Nat) (origin : Int) (leftTail rightTail : Nat) :
    denote (pathEnd code i) origin leftTail rightTail =
      ⟨IncrementSelector.literalState (i+2),origin+1,2*bits (pathLeft code) leftTail,false,rightTail⟩ := by
  simp [denote,pathEnd,bits,bitVal]

/-- A successful path check proves exact silent redispatch for arbitrary tape
tails. This theorem does not assume that an unchecked code is admissible. -/
theorem literal_redispatch_code (code : List Bool) (i : Nat)
    (hcheck : pathCheck code i = true) (origin : Int) (leftTail rightTail : Nat) :
    silent Record285.machine (pathCost code)
      (IncrementReturn.atLeftWord IncrementPreparation.dispatch0 (origin-1)
        (bits (pathLeft code) leftTail) (1+4*rightTail)) =
      some ⟨IncrementSelector.literalState (i+2),origin+1,2*bits (pathLeft code) leftTail,
        false,rightTail⟩ := by
  have hc : run (pathCost code) (pathStart code) = some (pathEnd code i) := by
    simpa only [pathCheck,decide_eq_true_eq] using hcheck
  have h := run_sound (pathCost code) (pathStart code) (pathEnd code i) hc origin leftTail rightTail
  simpa only [path_start_denote,path_end_denote] using h

theorem frozen_path_check (i : Nat) (hi : i < 15) : pathCheck (control i) i = true := by
  apply decide_eq_true_eq.mpr
  simpa only [pathCost,pathStart,pathEnd,pathLeft,controlLeft,dispatchCost,
    dispatchStart,dispatchEnd] using dispatch_check i hi

end Shared.PNP.Record285.SymbolicDispatch
