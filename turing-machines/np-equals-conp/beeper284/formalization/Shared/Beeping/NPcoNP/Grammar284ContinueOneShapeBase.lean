import Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch

/-! Finite restart shapes for the producer's `_continue.1` leaves. -/
namespace Shared.Beeping.NPcoNP.Grammar284ContinueOneShapeBase
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 200000000

def continueLeaves : List (Path × String) :=
  traceState557.acc.leaves.toList.filter (fun e => e.2 == "_continue.1")

def restartIndex (p : Path) : Option Nat :=
  ((p.zipIdx.reverse.filter fun e => e.2 ≥ 1 && e.1)[1]?).map Prod.snd

def continueOneCheck (entry : Path × String) : Bool :=
  match restartIndex entry.1, restart traceState557.acc.starts entry.1 1 with
  | some i, some dst =>
    match traceState557.acc.leaves[dst]? with
    | some (next,_) =>
      let base := entry.1.take i ++ [true]
      decide (1 ≤ i ∧ i+1<entry.1.length) && (entry.1[i]? == some true) &&
        (List.range' (i+1) (entry.1.length-1-(i+1))).all
          (fun j => entry.1[j]? == some false) &&
        (next == base ++ List.replicate (next.length-base.length) false)
    | none => false
  | _, _ => false

def rangeCheck (lo count : Nat) : Bool :=
  (List.range' lo count).all (fun i => match continueLeaves[i]? with
    | some entry => continueOneCheck entry
    | none => false)

theorem rangeCheck_sound (lo count i : Nat) (h : rangeCheck lo count=true)
    (lower : lo ≤ i) (upper : i<lo+count) (entry : Path × String)
    (he : continueLeaves[i]?=some entry) : continueOneCheck entry=true := by
  have hm : i ∈ List.range' lo count := by simp; omega
  have hh := List.all_eq_true.mp h i hm
  simpa only [rangeCheck, he] using hh
end Shared.Beeping.NPcoNP.Grammar284ContinueOneShapeBase
