import Shared.Beeping.NPcoNP.Grammar284ContinueOneShapeShard00
import Shared.Beeping.NPcoNP.Grammar284ContinueOneShapeShard01
import Shared.Beeping.NPcoNP.Grammar284ContinueOneShapeShard02

/-! Coverage and soundness of the finite `_continue.1` restart checks. -/
namespace Shared.Beeping.NPcoNP.Grammar284ContinueOneShape
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284ContinueOneShapeBase
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 200000000

theorem continue_count : continueLeaves.length=27 := by decide

theorem all_continue_one_shapes (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList)
    (name : entry.2="_continue.1") : continueOneCheck entry=true := by
  have mem : entry ∈ continueLeaves := by
    simp only [continueLeaves,List.mem_filter,beq_iff_eq]
    exact ⟨member,name⟩
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp mem
  have hie : continueLeaves[i]?=some entry := by rw [List.getElem?_eq_getElem hi,he]
  have bound : i<27 := by simpa only [continue_count] using hi
  by_cases h0 : i<10
  · exact rangeCheck_sound 0 10 i Grammar284ContinueOneShapeShard00.checked (by omega) (by omega) entry hie
  by_cases h1 : i<20
  · exact rangeCheck_sound 10 10 i Grammar284ContinueOneShapeShard01.checked (by omega) (by omega) entry hie
  exact rangeCheck_sound 20 7 i Grammar284ContinueOneShapeShard02.checked (by omega) (by omega) entry hie

theorem continue_one_shape_sound (entry : Path × String) (checked : continueOneCheck entry=true) :
    ∃ i dst next nextName, restartIndex entry.1=some i ∧
      restart traceState557.acc.starts entry.1 1=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      1 ≤ i ∧ i+1<entry.1.length ∧ entry.1[i]?=some true ∧
      (∀ j, i<j → j<entry.1.length-1 → entry.1[j]?=some false) ∧
      next=(entry.1.take i ++ [true]) ++
        List.replicate (next.length-(entry.1.take i ++ [true]).length) false := by
  cases hi : restartIndex entry.1 with
  | none => simp [continueOneCheck,hi] at checked
  | some i =>
    cases hd : restart traceState557.acc.starts entry.1 1 with
    | none => simp [continueOneCheck,hi,hd] at checked
    | some dst =>
      cases he : traceState557.acc.leaves[dst]? with
      | none => simp [continueOneCheck,hi,hd,he] at checked
      | some pair =>
        rcases pair with ⟨next,nextName⟩
        simp only [continueOneCheck,hi,hd,he,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at checked
        obtain ⟨⟨⟨⟨hl,hu⟩,hbit⟩,hall⟩,hshape⟩ := checked
        refine ⟨i,dst,next,nextName,rfl,rfl,he,hl,hu,hbit,?_,hshape⟩
        intro j hj hj'
        have hm : j ∈ List.range' (i+1) (entry.1.length-1-(i+1)) := by simp; omega
        simpa only [beq_iff_eq] using List.all_eq_true.mp hall j hm

#print axioms all_continue_one_shapes
#print axioms continue_one_shape_sound
end Shared.Beeping.NPcoNP.Grammar284ContinueOneShape
