import Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch

/-! Literal final control transitions for expanded administrative leaves.
The subsequent break and continue routines are separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeRightDispatchGeneric
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 100000000

/-- The literal entry state of each administrative routine after its final
control bit has been erased. -/
def administrativeEntry : String → Option (Fin 284)
  | "_break.1" => some 95
  | "_break.2" => some 96
  | "_continue.1" => some 97
  | "_continue.2" => some 98
  | _ => none

def administrativePathOK (entry : Path × String) : Bool :=
  match administrativeEntry entry.2 with
  | none => true
  | some r =>
    match followRight 93 entry.1.tail.dropLast with
    | none => false
    | some q => entry.1.tail.getLast? == some true &&
        decide (machine.table.row q true = ⟨false,.left,r,false⟩)

/-- Every listed administrative leaf has a true final bit and takes the
specified erase-left transition into its named routine. -/
theorem all_administrative_paths_checked :
    traceState557.acc.leaves.toList.all administrativePathOK = true := by
  decide

theorem administrative_path_checked (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList) (r : Fin 284)
    (target : administrativeEntry entry.2=some r) :
    ∃ q, followRight 93 entry.1.tail.dropLast=some q ∧
      entry.1.tail.getLast?=some true ∧
      machine.table.row q true=⟨false,.left,r,false⟩ := by
  have hc := List.all_eq_true.mp all_administrative_paths_checked entry member
  simp only [administrativePathOK,target] at hc
  cases hq : followRight 93 entry.1.tail.dropLast with
  | none => simp [hq] at hc
  | some q =>
    simp only [hq,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at hc
    exact ⟨q,rfl,hc.1,hc.2⟩

/-- A checked administrative path executes silently through the erasure of
its supplied final true cell. The tape is otherwise unchanged. -/
theorem administrative_dispatch (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList) (r : Fin 284)
    (target : administrativeEntry entry.2=some r) (h : Int) (t : Int → Bool)
    (layout : Holds t h entry.1.tail.dropLast)
    (last : t (h+(entry.1.tail.dropLast.length : Int))=true) :
    silentSegment machine (cfg 93 h t)
      (cfg r (h+(entry.1.tail.dropLast.length : Int)-1)
        ((cfg (93 : Fin 284) (h+(entry.1.tail.dropLast.length : Int)) t).write false))
      (entry.1.tail.dropLast.length+1) := by
  obtain ⟨q,hq,_hlast,hrow⟩ := administrative_path_checked entry member r target
  have first := dispatch 93 q h t entry.1.tail.dropLast hq layout
  have step : machine.step (cfg q (h+(entry.1.tail.dropLast.length : Int)) t) =
      (cfg r (h+(entry.1.tail.dropLast.length : Int)-1)
        ((cfg (93 : Fin 284) (h+(entry.1.tail.dropLast.length : Int)) t).write false),false) := by
    dsimp only [Machine.step,cfg]
    rw [last,hrow]
    rfl
  exact segAdd machine _ _ _ _ 1 first (oneSeg machine _ _ step)

/-- Every expanded leaf is covered by one of the ordinary or administrative
entry maps; the two maps do not both apply to a listed leaf. -/
theorem all_leaf_entry_maps_partition :
    traceState557.acc.leaves.toList.all (fun entry =>
      (operationEntry entry.2).isSome != (administrativeEntry entry.2).isSome) = true := by
  decide

/-- Split a supplied tape word at the end of a prefix. -/
theorem holds_split (t : Int → Bool) (h : Int) (xs ys : List Bool)
    (layout : Holds t h (xs++ys)) :
    Holds t h xs ∧ Holds t (h+(xs.length : Int)) ys := by
  induction xs generalizing h with
  | nil => simpa [Holds] using layout
  | cons b xs ih =>
    simp only [List.cons_append,Holds] at layout
    obtain ⟨hp,hs⟩ := ih (h+1) layout.2
    refine ⟨⟨layout.1,hp⟩,?_⟩
    simpa [List.length_cons,Nat.cast_add,Int.add_assoc,Int.add_comm,Int.add_left_comm] using hs

/-- The full-word version needs only the tape layout used for ordinary
leaves: its checked last bit supplies the erasure step. -/
theorem administrative_full_dispatch (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList) (r : Fin 284)
    (target : administrativeEntry entry.2=some r) (h : Int) (t : Int → Bool)
    (layout : Holds t h entry.1.tail) :
    silentSegment machine (cfg 93 h t)
      (cfg r (h+(entry.1.tail.dropLast.length : Int)-1)
        ((cfg (93 : Fin 284) (h+(entry.1.tail.dropLast.length : Int)) t).write false))
      (entry.1.tail.dropLast.length+1) := by
  obtain ⟨_,_,hlast,_⟩ := administrative_path_checked entry member r target
  have decomposition : entry.1.tail.dropLast ++ [true] = entry.1.tail :=
    List.dropLast_append_getLast? true (by simp [hlast])
  have whole : Holds t h (entry.1.tail.dropLast ++ [true]) := by
    rw [decomposition]
    exact layout
  obtain ⟨hp,hs⟩ := holds_split t h entry.1.tail.dropLast [true] whole
  have last : t (h+(entry.1.tail.dropLast.length : Int))=true := by
    simpa [Holds] using hs
  exact administrative_dispatch entry member r target h t hp last

/-- The administrative full-word theorem applies to the certified expansion. -/
theorem expanded_administrative_dispatch (e : Expansion)
    (expanded : expand producerGrammar.nodes 53 (.node producerGrammar.root)
      [true,true,false] [] {} = some e)
    (entry : Path × String) (member : entry ∈ e.leaves.toList) (r : Fin 284)
    (target : administrativeEntry entry.2=some r) (h : Int) (t : Int → Bool)
    (layout : Holds t h entry.1.tail) :
    silentSegment machine (cfg 93 h t)
      (cfg r (h+(entry.1.tail.dropLast.length : Int)-1)
        ((cfg (93 : Fin 284) (h+(entry.1.tail.dropLast.length : Int)) t).write false))
      (entry.1.tail.dropLast.length+1) := by
  rw [producerExpand] at expanded
  cases expanded
  exact administrative_full_dispatch entry member r target h t layout

#print axioms all_leaf_entry_maps_partition
#print axioms all_administrative_paths_checked
#print axioms administrative_dispatch
#print axioms expanded_administrative_dispatch
end Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
