import Shared.Beeping.NPcoNP.Grammar284ContinueTwoShapeShard00
import Shared.Beeping.NPcoNP.Grammar284ContinueTwoShapeShard01
import Shared.Beeping.NPcoNP.Grammar284ContinueTwoShapeShard02
import Shared.Beeping.NPcoNP.Grammar284ContinueTwoShapeShard03
import Shared.Beeping.NPcoNP.Grammar284ContinueTwoShapeShard04
import Shared.Beeping.NPcoNP.Grammar284ContinueTwoShapeShard05

/-! Coverage and soundness of the finite `_continue.2` restart checks. -/
namespace Shared.Beeping.NPcoNP.Grammar284ContinueTwoShape
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284ContinueTwoShapeBase
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 200000000

theorem continue_count : continueLeaves.length=60 := by decide

theorem all_continue_two_shapes (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList)
    (name : entry.2="_continue.2") : continueTwoCheck entry=true := by
  have mem : entry ∈ continueLeaves := by
    simp only [continueLeaves,List.mem_filter,beq_iff_eq]
    exact ⟨member,name⟩
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp mem
  have hie : continueLeaves[i]?=some entry := by rw [List.getElem?_eq_getElem hi,he]
  have bound : i<60 := by simpa only [continue_count] using hi
  by_cases h0 : i<10
  · exact rangeCheck_sound 0 10 i Grammar284ContinueTwoShapeShard00.checked (by omega) (by omega) entry hie
  by_cases h1 : i<20
  · exact rangeCheck_sound 10 10 i Grammar284ContinueTwoShapeShard01.checked (by omega) (by omega) entry hie
  by_cases h2 : i<30
  · exact rangeCheck_sound 20 10 i Grammar284ContinueTwoShapeShard02.checked (by omega) (by omega) entry hie
  by_cases h3 : i<40
  · exact rangeCheck_sound 30 10 i Grammar284ContinueTwoShapeShard03.checked (by omega) (by omega) entry hie
  by_cases h4 : i<50
  · exact rangeCheck_sound 40 10 i Grammar284ContinueTwoShapeShard04.checked (by omega) (by omega) entry hie
  exact rangeCheck_sound 50 10 i Grammar284ContinueTwoShapeShard05.checked (by omega) (by omega) entry hie

theorem continue_two_shape_sound (entry : Path × String) (checked : continueTwoCheck entry=true) :
    ∃ i j dst next nextName, restartIndex entry.1 2=some i ∧ restartIndex entry.1 1=some j ∧
      restart traceState557.acc.starts entry.1 2=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      1 ≤ i ∧ i<j ∧ j+1<entry.1.length ∧ entry.1[i]?=some true ∧ entry.1[j]?=some true ∧
      (∀ k, i<k → k<entry.1.length-1 → k≠j → entry.1[k]?=some false) ∧
      next=(entry.1.take i ++ [true]) ++
        List.replicate (next.length-(entry.1.take i ++ [true]).length) false := by
  cases hi : restartIndex entry.1 2 with
  | none => simp [continueTwoCheck,hi] at checked
  | some i =>
    cases hj : restartIndex entry.1 1 with
    | none => simp [continueTwoCheck,hi,hj] at checked
    | some j =>
      cases hd : restart traceState557.acc.starts entry.1 2 with
      | none => simp [continueTwoCheck,hi,hj,hd] at checked
      | some dst =>
        cases he : traceState557.acc.leaves[dst]? with
        | none => simp [continueTwoCheck,hi,hj,hd,he] at checked
        | some pair =>
          rcases pair with ⟨next,nextName⟩
          simp only [continueTwoCheck,hi,hj,hd,he,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at checked
          obtain ⟨⟨⟨⟨⟨hl,hij,hju⟩,hbit⟩,hmid⟩,hall⟩,hshape⟩ := checked
          refine ⟨i,j,dst,next,nextName,rfl,rfl,rfl,he,hl,hij,hju,hbit,hmid,?_,hshape⟩
          intro k hk hk' hne
          have hm : k ∈ List.range' (i+1) (entry.1.length-1-(i+1)) := by simp; omega
          have hs := List.all_eq_true.mp hall k hm
          simpa only [Bool.or_eq_true,beq_iff_eq,hne,false_or] using hs

#print axioms all_continue_two_shapes
#print axioms continue_two_shape_sound
end Shared.Beeping.NPcoNP.Grammar284ContinueTwoShape
