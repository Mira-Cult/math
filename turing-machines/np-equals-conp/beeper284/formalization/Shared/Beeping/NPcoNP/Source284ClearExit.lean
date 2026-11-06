import Shared.Beeping.NPcoNP.Source284OrientedExit

/-! A two-step detector exit clears the current source cell and its physical
predecessor. It uses the stopped compiler orientation to move toward the
predecessor, then turns back facing the tagged buffer. The continuation starts
in orientation false. This is an auxiliary finite source table, not the record
table. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284ClearExit

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284DetectorProduct (allocated)
open Shared.Beeping.NPcoNP.Source284DetectorExit (stopping stopConfig entry)
open Shared.Beeping.NPcoNP.Source284OrientedExit (side)

/-- In the first exit row, orientation zero turns toward the predecessor;
orientation one continues toward it. The second row clears that predecessor
and turns back. -/
def table (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (q : Nat) (b : Bool) : Row :=
  if q < allocated states then
    if stopping marks q then ⟨false,decide (side q = 0),some (allocated states)⟩
    else Source284DetectorProduct.table states marks original q b
  else if q = allocated states then ⟨false,true,some (entry states)⟩
  else shiftRow (entry states) (continuation (q-entry states) b)

/-- Clearing changes writes and movement, never control destinations. -/
theorem next_eq (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (q : Nat) (b : Bool) :
    (table states marks original continuation q b).next =
      (Source284DetectorExit.table states marks original continuation q b).next := by
  by_cases hq : q < allocated states
  · by_cases hs : stopping marks q = true
    · simp [table,Source284DetectorExit.table,hq,hs]
    · have hf : stopping marks q = false := Bool.eq_false_iff.mpr hs
      simp [table,Source284DetectorExit.table,hq,hf]
  · by_cases he : q = allocated states <;> simp [table,Source284DetectorExit.table,hq,he]

theorem closed (states continuationStates : Nat) (marks : List Bool)
    (original continuation : Nat → Bool → Row) (hn : 0 < continuationStates)
    (ho : Closed states original) (hc : Closed continuationStates continuation) :
    Closed (entry states+continuationStates) (table states marks original continuation) := by
  intro q hq b q' hnext
  apply Source284DetectorExit.closed states continuationStates marks original continuation hn ho hc q hq b q'
  simpa only [← next_eq] using hnext

theorem step_before (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (c : Config) (hc : Valid (allocated states) c) (hs : ¬ stopConfig marks c) :
    step (table states marks original continuation) c =
      step (Source284DetectorProduct.table states marks original) c := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      have hq := hc q rfl
      have hf : stopping marks q = false := by
        cases he : stopping marks q with
        | false => rfl
        | true => exact False.elim (hs ⟨q,rfl,he⟩)
      simp [step,table,hq,hf]

/-- Exact two-step effect for either orientation. The final source direction
points toward the former physical right side in both cases. -/
theorem clear_two (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (left right q : Nat) (hq : q < allocated states) (hs : stopping marks q = true) :
    run (table states marks original continuation) ⟨left,right,some q⟩ 2 =
      if side q = 0 then ⟨2*(left/2),2*(right/2),some (entry states)⟩
      else ⟨2*((right/2)/2),2*left,some (entry states)⟩ := by
  by_cases hside : side q = 0
  · simp [run,step,table,hq,hs,hside,entry,bit]
  · simp [run,step,table,hq,hs,hside,entry,bit]

theorem relocated_row (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (q : Nat) (b : Bool) :
    table states marks original continuation (entry states+q) b =
      shiftRow (entry states) (continuation q b) := by
  have h0 : ¬ entry states+q < allocated states := by simp [entry]; omega
  have h1 : entry states+q ≠ allocated states := by simp [entry]; omega
  simp [table,h0,h1]

theorem relocated_step (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (c : Config) :
    step (table states marks original continuation) (shiftConfig (entry states) c) =
      shiftConfig (entry states) (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (c : Config) (fuel : Nat) :
    run (table states marks original continuation) (shiftConfig (entry states) c) fuel =
      shiftConfig (entry states) (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

def cleared (q : Nat) (c : Config) : Config :=
  if side q = 0 then ⟨2*(c.left/2),2*(c.right/2),some 0⟩
  else ⟨2*((c.right/2)/2),2*c.left,some 0⟩

theorem run_before (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (c : Config) (hc : Valid (allocated states) c) (ho : Closed states original) (n : Nat)
    (hs : ∀ i < n, ¬ stopConfig marks (run (Source284DetectorProduct.table states marks original) c i)) :
    run (table states marks original continuation) c n =
      run (Source284DetectorProduct.table states marks original) c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run]
    rw [ih (by intro i hi; exact hs i (by omega))]
    apply step_before states marks original continuation
    · exact valid_run _ _ c (Source284DetectorProduct.closed states marks original ho) hc n
    · exact hs n (by omega)

/-- The first stopping visit is followed by the two clearing transitions and
then by every step of the supplied continuation. -/
theorem run_first_stop (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (c : Config) (hc : Valid (allocated states) c) (ho : Closed states original) (n fuel q : Nat)
    (hbefore : ∀ i < n, ¬ stopConfig marks (run (Source284DetectorProduct.table states marks original) c i))
    (hq : (run (Source284DetectorProduct.table states marks original) c n).state = some q)
    (hs : stopping marks q = true) :
    let last := run (Source284DetectorProduct.table states marks original) c n
    run (table states marks original continuation) c (n+2+fuel) =
      shiftConfig (entry states) (run continuation (cleared q last) fuel) := by
  dsimp only
  have hvalid := valid_run _ _ c (Source284DetectorProduct.closed states marks original ho) hc n
  have hq' := hvalid q hq
  let last := run (Source284DetectorProduct.table states marks original) c n
  have hqLast : last.state = some q := hq
  have hconfig : last = ⟨last.left,last.right,some q⟩ := by
    cases h : last with
    | mk left right state => simp [h] at hqLast ⊢; exact hqLast
  have he := clear_two states marks original continuation last.left last.right q hq' hs
  rw [← hconfig] at he
  have he' : run (table states marks original continuation) last 2 =
      shiftConfig (entry states) (cleared q last) := by
    rw [he]
    by_cases h : side q = 0 <;> simp [cleared,shiftConfig,h]
  rw [Source284HardwireCorrect.run_add,Source284HardwireCorrect.run_add,
    run_before states marks original continuation c hc ho n hbefore,he',relocated_run]

namespace Fixtures
def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
example : run (table 2 [true,true] loop loop) ⟨5,7,some (Nat.pair 8 0)⟩ 2 =
    ⟨4,6,some (entry 2)⟩ := by decide +kernel
example : run (table 2 [true,true] loop loop) ⟨5,7,some (Nat.pair 8 1)⟩ 2 =
    ⟨2,10,some (entry 2)⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284ClearExit
