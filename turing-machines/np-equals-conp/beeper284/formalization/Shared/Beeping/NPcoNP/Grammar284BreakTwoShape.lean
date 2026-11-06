import Shared.Beeping.NPcoNP.Grammar284SuccessorShape

/-! Finite control-word shapes for the single expanded `_break.2` leaves. -/
namespace Shared.Beeping.NPcoNP.Grammar284BreakTwoShape
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284SuccessorShapeBase
open Shared.Beeping.NPcoNP.Grammar284SuccessorShape
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 200000000

def breakLeaves : List (Path × String) :=
  traceState557.acc.leaves.toList.filter (fun e => e.2 == "_break.2")

def breakTwoCheck (entry : Path × String) : Bool :=
  match carryIndex entry.1 2, carryIndex entry.1 1 with
  | some i, some j =>
    decide (2 ≤ i ∧ i<j ∧ j+2<entry.1.length) &&
      (entry.1[i]? == some false) && (entry.1[j]? == some false) && (entry.1[entry.1.length-2]? == some false) &&
      (List.range' (i+1) (j-(i+1))).all (fun k => entry.1[k]? == some true) &&
      (List.range' (j+1) (entry.1.length-2-(j+1))).all (fun k => entry.1[k]? == some true) &&
      successorShape entry.1 2
  | _, _ => false

theorem break_count : breakLeaves.length=1 := by decide

theorem all_break_two_shapes : breakLeaves.all breakTwoCheck=true := by decide

theorem break_two_shape_sound (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList) (name : entry.2="_break.2") :
    ∃ i j dst next nextName,
      carryIndex entry.1 2=some i ∧ carryIndex entry.1 1=some j ∧
      successor traceState557.acc.starts entry.1 2=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      2 ≤ i ∧ i<j ∧ j+2<entry.1.length ∧ entry.1[i]?=some false ∧ entry.1[j]?=some false ∧ entry.1[entry.1.length-2]?=some false ∧
      (∀ k, i<k → k<j → entry.1[k]?=some true) ∧
      (∀ k, j<k → k<entry.1.length-2 → entry.1[k]?=some true) ∧
      next=(entry.1.take i ++ [true]) ++
        List.replicate (next.length-(entry.1.take i ++ [true]).length) false := by
  have mem : entry ∈ breakLeaves := by
    simp only [breakLeaves,List.mem_filter,beq_iff_eq]
    exact ⟨member,name⟩
  have hc := List.all_eq_true.mp all_break_two_shapes entry mem
  cases hi : carryIndex entry.1 2 with
  | none => simp [breakTwoCheck,hi] at hc
  | some i =>
    cases hj : carryIndex entry.1 1 with
    | none => simp [breakTwoCheck,hi,hj] at hc
    | some j =>
      simp only [breakTwoCheck,hi,hj,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨hlo,hij,hju⟩,hbit⟩,hmid⟩,hlastzero⟩,hall1⟩,hall2⟩,hshape⟩ := hc
      obtain ⟨i',dst,next,nextName,hi',hsucc,hnext,hword⟩ := successor_shape_sound entry.1 2 hshape
      rw [hi] at hi'
      have he : i'=i := Option.some.inj hi'.symm
      subst i'
      refine ⟨i,j,dst,next,nextName,rfl,rfl,hsucc,hnext,hlo,hij,hju,hbit,hmid,hlastzero,?_,?_,hword⟩
      · intro k hk hk'
        have hm : k ∈ List.range' (i+1) (j-(i+1)) := by simp; omega
        simpa only [beq_iff_eq] using List.all_eq_true.mp hall1 k hm
      · intro k hk hk'
        have hm : k ∈ List.range' (j+1) (entry.1.length-2-(j+1)) := by simp; omega
        simpa only [beq_iff_eq] using List.all_eq_true.mp hall2 k hm

#print axioms break_two_shape_sound
end Shared.Beeping.NPcoNP.Grammar284BreakTwoShape
