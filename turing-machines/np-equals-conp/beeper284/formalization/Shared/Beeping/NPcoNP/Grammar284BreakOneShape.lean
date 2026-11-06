import Shared.Beeping.NPcoNP.Grammar284SuccessorShape

/-! Finite control-word shapes for the six expanded `_break.1` leaves. -/
namespace Shared.Beeping.NPcoNP.Grammar284BreakOneShape
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284SuccessorShapeBase
open Shared.Beeping.NPcoNP.Grammar284SuccessorShape
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 200000000

def breakLeaves : List (Path × String) :=
  traceState557.acc.leaves.toList.filter (fun e => e.2 == "_break.1")

def breakOneCheck (entry : Path × String) : Bool :=
  match carryIndex entry.1 1, carryIndex entry.1 0 with
  | some i, some j =>
    decide (2 ≤ i ∧ i<j ∧ j+1<entry.1.length) &&
      (entry.1[i]? == some false) && (entry.1[j]? == some false) &&
      (List.range' (i+1) (j-(i+1))).all (fun k => entry.1[k]? == some true) &&
      (List.range' (j+1) (entry.1.length-1-(j+1))).all (fun k => entry.1[k]? == some true) &&
      successorShape entry.1 1
  | _, _ => false

theorem break_count : breakLeaves.length=6 := by decide

theorem all_break_one_shapes : breakLeaves.all breakOneCheck=true := by decide

theorem break_one_shape_sound (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList) (name : entry.2="_break.1") :
    ∃ i j dst next nextName,
      carryIndex entry.1 1=some i ∧ carryIndex entry.1 0=some j ∧
      successor traceState557.acc.starts entry.1 1=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      2 ≤ i ∧ i<j ∧ j+1<entry.1.length ∧ entry.1[i]?=some false ∧ entry.1[j]?=some false ∧
      (∀ k, i<k → k<j → entry.1[k]?=some true) ∧
      (∀ k, j<k → k<entry.1.length-1 → entry.1[k]?=some true) ∧
      next=(entry.1.take i ++ [true]) ++
        List.replicate (next.length-(entry.1.take i ++ [true]).length) false := by
  have mem : entry ∈ breakLeaves := by
    simp only [breakLeaves,List.mem_filter,beq_iff_eq]
    exact ⟨member,name⟩
  have hc := List.all_eq_true.mp all_break_one_shapes entry mem
  cases hi : carryIndex entry.1 1 with
  | none => simp [breakOneCheck,hi] at hc
  | some i =>
    cases hj : carryIndex entry.1 0 with
    | none => simp [breakOneCheck,hi,hj] at hc
    | some j =>
      simp only [breakOneCheck,hi,hj,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨hlo,hij,hju⟩,hbit⟩,hmid⟩,hall1⟩,hall2⟩,hshape⟩ := hc
      obtain ⟨i',dst,next,nextName,hi',hsucc,hnext,hword⟩ := successor_shape_sound entry.1 1 hshape
      rw [hi] at hi'
      have he : i'=i := Option.some.inj hi'.symm
      subst i'
      refine ⟨i,j,dst,next,nextName,rfl,rfl,hsucc,hnext,hlo,hij,hju,hbit,hmid,?_,?_,hword⟩
      · intro k hk hk'
        have hm : k ∈ List.range' (i+1) (j-(i+1)) := by simp; omega
        simpa only [beq_iff_eq] using List.all_eq_true.mp hall1 k hm
      · intro k hk hk'
        have hm : k ∈ List.range' (j+1) (entry.1.length-1-(j+1)) := by simp; omega
        simpa only [beq_iff_eq] using List.all_eq_true.mp hall2 k hm

#print axioms break_one_shape_sound
end Shared.Beeping.NPcoNP.Grammar284BreakOneShape
