import Shared.Beeping.NPcoNP.Source284UnaryMarkOne

/-! Reach and mark a second unary-pair block behind a first block's sentinel.
The original scratch boundary is marked before the scan, allowing the existing
marker to return across the outer block. Returning across the inner block is a
separate operation; these theorems expose its exact intermediate configuration. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284NestedMarker

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)
open Shared.Beeping.NPcoNP.Source284PayloadLoop (scratch)
open Shared.Beeping.NPcoNP.Source284ScratchScanner (push)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def enterMarker (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then shiftRow 1 (Source284UnaryMarkOne.table continuation 1 b)
  else shiftRow 1 (Source284UnaryMarkOne.table continuation (q-1) b)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨true,true,some 2⟩
  else shiftRow 1 (Source284ScratchScanner.table (enterMarker continuation) (q-1) b)

theorem marker_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    enterMarker continuation (1+q) b = shiftRow 1 (Source284UnaryMarkOne.table continuation q b) := by
  simp [enterMarker]

theorem marker_step (continuation : Nat → Bool → Row) (c : Config) :
    step (enterMarker continuation) (shiftConfig 1 c) =
      shiftConfig 1 (step (Source284UnaryMarkOne.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,marker_row,shiftRow]
      split <;> rfl

theorem marker_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (enterMarker continuation) (shiftConfig 1 c) fuel =
      shiftConfig 1 (run (Source284UnaryMarkOne.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,marker_step]

theorem marker_jump (continuation : Nat → Bool → Row) (left right fuel : Nat) :
    run (enterMarker continuation) ⟨left,right,some 0⟩ (fuel+1) =
      shiftConfig 1 (run (Source284UnaryMarkOne.table continuation)
        ⟨left,right,some 1⟩ (fuel+1)) := by
  rw [run_front,run_front]
  have hs : step (enterMarker continuation) ⟨left,right,some 0⟩ =
      shiftConfig 1 (step (Source284UnaryMarkOne.table continuation) ⟨left,right,some 1⟩) := by
    simp [step,enterMarker,shiftRow,shiftConfig]
    split <;> rfl
  rw [hs,marker_run]

theorem scanner_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (1+q) b =
      shiftRow 1 (Source284ScratchScanner.table (enterMarker continuation) q b) := by
  simp [table]

theorem scanner_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 1 c) =
      shiftConfig 1 (step (Source284ScratchScanner.table (enterMarker continuation)) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,scanner_row,shiftRow]
      split <;> rfl

theorem scanner_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 1 c) fuel =
      shiftConfig 1 (run (Source284ScratchScanner.table (enterMarker continuation)) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,scanner_step]

/-- Paid scan to the outer block, retaining a boundary marker. -/
theorem scan (continuation : Nat → Bool → Row) (inner : List Bool)
    (outer stream : Nat) :
    run (table continuation) ⟨pairTape inner outer,2*stream,some 0⟩ (2*inner.length+3) =
      ⟨4*push (2*stream+1) inner+1,outer,some 4⟩ := by
  have ht : 2*inner.length+3 = 1+(2*inner.length+2) := by omega
  rw [ht,Source284ScratchScanner.run_add]
  change run (table continuation) (step (table continuation)
    ⟨pairTape inner outer,2*stream,some 0⟩) _ = _
  have hs : step (table continuation) ⟨pairTape inner outer,2*stream,some 0⟩ =
      shiftConfig 1 ⟨2*stream+1,pairTape inner outer,some 1⟩ := by
    simp [step,table,shiftConfig,bit,Nat.testBit_zero]
  rw [hs,scanner_run]
  have hm : Source284ScratchTerminator.mark (4*outer) = 4*outer+2 := by
    simp [Source284ScratchTerminator.mark]
  have hd : (4*outer)/4 = outer := by omega
  have hh := Source284ScratchScanner.scan (enterMarker continuation) inner (2*stream+1) (4*outer)
  rw [hm,hd] at hh
  change run (Source284ScratchScanner.table (enterMarker continuation))
    ⟨2*stream+1,pairTape inner outer,some 1⟩ _ = _ at hh
  rw [hh]
  rfl


theorem enter_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 2 ≤ states) (hv : Closed states continuation) :
    Closed (13+states) (enterMarker continuation) := by
  have hm := Source284UnaryMarkOne.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q=0
  · subst q
    have he : (shiftRow 1 (Source284UnaryMarkOne.table continuation 1 b)).next = some q' := by
      simpa [enterMarker] using hnext
    cases hh : (Source284UnaryMarkOne.table continuation 1 b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hm 1 (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega
  · have he : (shiftRow 1 (Source284UnaryMarkOne.table continuation (q-1) b)).next = some q' := by
      simpa [enterMarker,h0] using hnext
    cases hh : (Source284UnaryMarkOne.table continuation (q-1) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hm (q-1) (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 2 ≤ states) (hv : Closed states continuation) :
    Closed (17+states) (table continuation) := by
  have hs := Source284ScratchScanner.closed (13+states) (enterMarker continuation) (by omega)
    (enter_closed states continuation hn hv)
  intro q hq b q' hnext
  by_cases h0 : q=0
  · subst q; simp [table] at hnext; omega
  · have he : (shiftRow 1 (Source284ScratchScanner.table (enterMarker continuation) (q-1) b)).next = some q' := by
      simpa [table,h0] using hnext
    cases hh : (Source284ScratchScanner.table (enterMarker continuation) (q-1) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hs (q-1) (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega

/-- After the inner scan, mark the first unmarked outer token. The inner
block is retained on the opposite tape half for a subsequent return pass. -/
theorem mark_outer (continuation : Nat → Bool → Row) (inner : List Bool)
    (k : Nat) (rest : List Bool) (certificate stream : Nat) :
    run (table continuation)
      ⟨pairTape inner (pairTape (List.replicate k true ++ false::rest) certificate),
        2*stream,some 0⟩ (2*inner.length+4*k+8) =
    ⟨pairTape (List.replicate k true ++ true::rest) certificate,
      4*push (2*stream+1) inner,some 17⟩ := by
  have ht : 2*inner.length+4*k+8 = (2*inner.length+3)+(4*k+5) := by omega
  rw [ht,Source284ScratchScanner.run_add,scan]
  change run (table continuation) (shiftConfig 1
    (shiftConfig 3 ⟨4*push (2*stream+1) inner+1,
      pairTape (List.replicate k true ++ false::rest) certificate,some 0⟩)) _ = _
  rw [scanner_run,Source284ScratchScanner.relocated_run]
  have hh := Source284UnaryMarkOne.mark_first continuation k rest certificate (2*push (2*stream+1) inner)
  have he : 4*k+6 = 1+(4*k+5) := by omega
  rw [he,Source284ScratchScanner.run_add] at hh
  change run (Source284UnaryMarkOne.table continuation)
    (step (Source284UnaryMarkOne.table continuation)
      ⟨pairTape (List.replicate k true ++ false::rest) certificate,
        2*(2*push (2*stream+1) inner),some 0⟩) _ = _ at hh
  rw [Source284UnaryMarkOne.startup] at hh
  have hc : 4*k+5 = (4*k+4)+1 := by omega
  rw [hc,marker_jump,← hc]
  have hp : 2*(2*push (2*stream+1) inner)+1 = 4*push (2*stream+1) inner+1 := by omega
  rw [hp] at hh
  rw [hh]
  simp [shiftConfig]
  omega

/-- The exhaustion branch preserves the outer block and reports state 18. -/
theorem outer_exhausted (continuation : Nat → Bool → Row) (inner : List Bool)
    (k certificate stream : Nat) :
    run (table continuation)
      ⟨pairTape inner (pairTape (List.replicate k true) certificate),2*stream,some 0⟩
      (2*inner.length+4*k+8) =
    ⟨pairTape (List.replicate k true) certificate,
      4*push (2*stream+1) inner,some 18⟩ := by
  have ht : 2*inner.length+4*k+8 = (2*inner.length+3)+(4*k+5) := by omega
  rw [ht,Source284ScratchScanner.run_add,scan]
  change run (table continuation) (shiftConfig 1
    (shiftConfig 3 ⟨4*push (2*stream+1) inner+1,
      pairTape (List.replicate k true) certificate,some 0⟩)) _ = _
  rw [scanner_run,Source284ScratchScanner.relocated_run]
  have hh := Source284UnaryMarkOne.all_marked continuation k certificate (2*push (2*stream+1) inner)
  have he : 4*k+6 = 1+(4*k+5) := by omega
  rw [he,Source284ScratchScanner.run_add] at hh
  change run (Source284UnaryMarkOne.table continuation)
    (step (Source284UnaryMarkOne.table continuation)
      ⟨pairTape (List.replicate k true) certificate,
        2*(2*push (2*stream+1) inner),some 0⟩) _ = _ at hh
  rw [Source284UnaryMarkOne.startup] at hh
  have hc : 4*k+5 = (4*k+4)+1 := by omega
  rw [hc,marker_jump,← hc]
  have hp : 2*(2*push (2*stream+1) inner)+1 = 4*push (2*stream+1) inner+1 := by omega
  rw [hp] at hh
  rw [hh]
  simp [shiftConfig]
  omega


/-- Both marker outcomes are runs of a finite encoded source description. -/
theorem source_mark_outer (states : Nat) (continuation : Nat → Bool → Row) (inner : List Bool)
    (k : Nat) (rest : List Bool) (certificate stream : Nat) (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (encode (17+states) (table continuation) 1)
      (Source284Relative.initial (2*stream)
        (pairTape inner (pairTape (List.replicate k true ++ false::rest) certificate)))
      (2*inner.length+4*k+8) =
    ⟨pairTape (List.replicate k true ++ true::rest) certificate,
      4*push (2*stream+1) inner,active 17⟩ := by
  let start : Config := ⟨pairTape inner (pairTape (List.replicate k true ++ false::rest) certificate),
    2*stream,some 0⟩
  have hi : Valid (17+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (17+states) (table continuation) 1 start (closed states continuation hn hv)
    hi (2*inner.length+4*k+8)
  rw [mark_outer] at hr
  exact hr

theorem source_outer_exhausted (states : Nat) (continuation : Nat → Bool → Row) (inner : List Bool)
    (k certificate stream : Nat) (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (encode (17+states) (table continuation) 1)
      (Source284Relative.initial (2*stream) (pairTape inner (pairTape (List.replicate k true) certificate)))
      (2*inner.length+4*k+8) =
    ⟨pairTape (List.replicate k true) certificate,4*push (2*stream+1) inner,active 18⟩ := by
  let start : Config := ⟨pairTape inner (pairTape (List.replicate k true) certificate),2*stream,some 0⟩
  have hi : Valid (17+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (17+states) (table continuation) 1 start (closed states continuation hn hv)
    hi (2*inner.length+4*k+8)
  rw [outer_exhausted] at hr
  exact hr

namespace Fixtures

def loop (q : Nat) (b : Bool) : Row := ⟨b,false,some q⟩
example : run (table loop) ⟨pairTape [] (pairTape [false] 3),0,some 0⟩ 8 =
    ⟨pairTape [true] 3,4,some 17⟩ := by decide +kernel
example : run (table loop) ⟨pairTape [] (pairTape [] 3),0,some 0⟩ 8 =
    ⟨pairTape [] 3,4,some 18⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284NestedMarker
