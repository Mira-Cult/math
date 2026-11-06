import Shared.Beeping.NPcoNP.Grammar284GraphOperation

/-! Finite grammar successor shapes for ordinary producer graph rows. The
special graph-root return and physical administrative routing remain separate. -/
namespace Shared.Beeping.NPcoNP.Grammar284SuccessorShapeBase
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 200000000

/-- Index of the selected false control bit, counting from the right and
excluding the two root header bits. -/
def carryIndex (path : Path) (skip : Nat) : Option Nat :=
  ((path.zipIdx.reverse.filter fun e => e.2 ≥ 2 && !e.1)[skip]?).map Prod.snd

/-- Check that the grammar successor's first expanded leaf has the carried
prefix followed only by zero bits. -/
def successorShape (path : Path) (skip : Nat) : Bool :=
  match carryIndex path skip, successor traceState557.acc.starts path skip with
  | some i, some dst =>
    match traceState557.acc.leaves[dst]? with
    | some entry =>
      let base := path.take i ++ [true]
      entry.1 == base ++ List.replicate (entry.1.length-base.length) false
    | none => false
  | _, _ => false

/-- The selected false bit is the last false bit before the branch's carry
cutoff. For a zero decrement the final false bit is excluded. -/
def rightmostOK (path : Path) (skip : Nat) : Bool :=
  match carryIndex path skip with
  | none => false
  | some i =>
    let cutoff := path.length-skip
    decide (2 ≤ i ∧ i<cutoff) && (path[i]? == some false) &&
      (List.range' (i+1) (cutoff-(i+1))).all (fun j => path[j]? == some true)

/-- At non-root-return ordinary rows, increment and the positive decrement
use the first false bit; zero decrement uses the second. -/
def ordinaryStateShape (state : Fin 185) : Bool :=
  if state.val == 184 then true else
    match graphLeaf state with
    | none => false
    | some (path,name) =>
      match namedOperation name with
      | none => true
      | some (_,true) => successorShape path 0 && rightmostOK path 0
      | some (_,false) => successorShape path 0 && rightmostOK path 0 && successorShape path 1 &&
          rightmostOK path 1 && (path.getLast? == some false)

/-- A bounded segment of the finite graph-state check. -/
def rangeCheck (lo count : Nat) : Bool :=
  (List.range' lo count).all (fun i => if hi : i<185 then ordinaryStateShape ⟨i,hi⟩ else true)

theorem rangeCheck_sound (lo count : Nat) (h : rangeCheck lo count=true)
    (state : Fin 185) (lower : lo≤state.val) (upper : state.val<lo+count) :
    ordinaryStateShape state=true := by
  have hm : state.val ∈ List.range' lo count := by simp; omega
  have hh := List.all_eq_true.mp h state.val hm
  simpa only [rangeCheck, dif_pos state.isLt] using hh

end Shared.Beeping.NPcoNP.Grammar284SuccessorShapeBase
