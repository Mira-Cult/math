import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard00
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard01
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard02
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard03
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard04
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard05
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard06
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard07
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard08
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard09
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard10
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard11
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard12
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard13
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard14
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard15
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard16
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard17
import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeShard18

/-! Coverage of the bounded ordinary-branch successor shape checks. -/
namespace Shared.Beeping.NPcoNP.Grammar284SuccessorShape
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284SuccessorShapeBase
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 100000000

/-- Every bounded state passes its ordinary successor shape check. The root
return is excluded in the definition of the check. -/
theorem all_ordinary_successor_shapes (state : Fin 185) : ordinaryStateShape state=true := by
  by_cases h0 : state.val<10
  · exact rangeCheck_sound 0 10 Grammar284SuccessorShapeShard00.checked state (by omega) (by omega)
  by_cases h1 : state.val<20
  · exact rangeCheck_sound 10 10 Grammar284SuccessorShapeShard01.checked state (by omega) (by omega)
  by_cases h2 : state.val<30
  · exact rangeCheck_sound 20 10 Grammar284SuccessorShapeShard02.checked state (by omega) (by omega)
  by_cases h3 : state.val<40
  · exact rangeCheck_sound 30 10 Grammar284SuccessorShapeShard03.checked state (by omega) (by omega)
  by_cases h4 : state.val<50
  · exact rangeCheck_sound 40 10 Grammar284SuccessorShapeShard04.checked state (by omega) (by omega)
  by_cases h5 : state.val<60
  · exact rangeCheck_sound 50 10 Grammar284SuccessorShapeShard05.checked state (by omega) (by omega)
  by_cases h6 : state.val<70
  · exact rangeCheck_sound 60 10 Grammar284SuccessorShapeShard06.checked state (by omega) (by omega)
  by_cases h7 : state.val<80
  · exact rangeCheck_sound 70 10 Grammar284SuccessorShapeShard07.checked state (by omega) (by omega)
  by_cases h8 : state.val<90
  · exact rangeCheck_sound 80 10 Grammar284SuccessorShapeShard08.checked state (by omega) (by omega)
  by_cases h9 : state.val<100
  · exact rangeCheck_sound 90 10 Grammar284SuccessorShapeShard09.checked state (by omega) (by omega)
  by_cases h10 : state.val<110
  · exact rangeCheck_sound 100 10 Grammar284SuccessorShapeShard10.checked state (by omega) (by omega)
  by_cases h11 : state.val<120
  · exact rangeCheck_sound 110 10 Grammar284SuccessorShapeShard11.checked state (by omega) (by omega)
  by_cases h12 : state.val<130
  · exact rangeCheck_sound 120 10 Grammar284SuccessorShapeShard12.checked state (by omega) (by omega)
  by_cases h13 : state.val<140
  · exact rangeCheck_sound 130 10 Grammar284SuccessorShapeShard13.checked state (by omega) (by omega)
  by_cases h14 : state.val<150
  · exact rangeCheck_sound 140 10 Grammar284SuccessorShapeShard14.checked state (by omega) (by omega)
  by_cases h15 : state.val<160
  · exact rangeCheck_sound 150 10 Grammar284SuccessorShapeShard15.checked state (by omega) (by omega)
  by_cases h16 : state.val<170
  · exact rangeCheck_sound 160 10 Grammar284SuccessorShapeShard16.checked state (by omega) (by omega)
  by_cases h17 : state.val<180
  · exact rangeCheck_sound 170 10 Grammar284SuccessorShapeShard17.checked state (by omega) (by omega)
  exact rangeCheck_sound 180 5 Grammar284SuccessorShapeShard18.checked state (by omega) (by omega)

/-- Each applicable non-root ordinary branch has the checked successor and
rightmost-zero properties. -/
theorem ordinary_successor_shapes (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (increment : Bool) (operation : namedOperation name=some (n,increment)) :
    successorShape path 0=true ∧ rightmostOK path 0=true ∧
      (increment=false → successorShape path 1=true ∧ rightmostOK path 1=true ∧ path.getLast?=some false) := by
  have h := all_ordinary_successor_shapes state
  cases increment with
  | false =>
    simp [ordinaryStateShape,notRoot,leaf,operation] at h
    exact ⟨by tauto,by tauto,fun _ => by tauto⟩
  | true =>
    simp [ordinaryStateShape,notRoot,leaf,operation] at h
    exact ⟨h.1,h.2,by intro impossible; cases impossible⟩

/-- Extract the selected false bit and the all-one suffix before the carry
cutoff from the finite check. -/
theorem rightmost_sound (path : Path) (skip : Nat) (checked : rightmostOK path skip=true) :
    ∃ i, carryIndex path skip=some i ∧ 2 ≤ i ∧ i<path.length-skip ∧
      path[i]?=some false ∧ ∀ j, i<j → j<path.length-skip → path[j]?=some true := by
  cases hi : carryIndex path skip with
  | none => simp [rightmostOK,hi] at checked
  | some i =>
    simp only [rightmostOK,hi,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at checked
    obtain ⟨⟨⟨hl,hu⟩,hz⟩,hall⟩ := checked
    refine ⟨i,rfl,hl,hu,hz,?_⟩
    intro j hj hj'
    have hm : j ∈ List.range' (i+1) (path.length-skip-(i+1)) := by simp; omega
    simpa only [beq_iff_eq] using List.all_eq_true.mp hall j hm

/-- Extract the selected index and exact next leaf word from a successful
shape check. -/
theorem successor_shape_sound (path : Path) (skip : Nat)
    (checked : successorShape path skip=true) :
    ∃ i dst next name, carryIndex path skip=some i ∧
      successor traceState557.acc.starts path skip=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,name) ∧
      next=(path.take i ++ [true]) ++
        List.replicate (next.length-(path.take i ++ [true]).length) false := by
  cases hi : carryIndex path skip with
  | none => simp [successorShape,hi] at checked
  | some i =>
    cases hd : successor traceState557.acc.starts path skip with
    | none => simp [successorShape,hi,hd] at checked
    | some dst =>
      cases he : traceState557.acc.leaves[dst]? with
      | none => simp [successorShape,hi,hd,he] at checked
      | some entry =>
        rcases entry with ⟨next,name⟩
        simp only [successorShape,hi,hd,he,beq_iff_eq] at checked
        exact ⟨i,dst,next,name,rfl,rfl,he,checked⟩

#print axioms all_ordinary_successor_shapes
#print axioms ordinary_successor_shapes
#print axioms rightmost_sound
#print axioms successor_shape_sound
end Shared.Beeping.NPcoNP.Grammar284SuccessorShape
