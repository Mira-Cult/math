import Shared.Beeping.NPcoNP.Source284MatchDispatch
import Shared.Beeping.NPcoNP.Source284UnaryMarkOne

/-! One finite comparison step across both tape halves. Its four distinct
continuation entries report whether a unary token and a payload bit were
available. A mismatched branch may mark the available side. -/
set_option maxRecDepth 2048
namespace Shared.Beeping.NPcoNP.Source284MatchStep

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284UnaryMarkOne.table (Source284MatchDispatch.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 4 ≤ states) (hv : Closed states continuation) : Closed (48+states) (table continuation) := by
  have hd := Source284MatchDispatch.closed states continuation hn hv
  have hu := Source284UnaryMarkOne.closed (36+states) (Source284MatchDispatch.table continuation) (by omega) hd
  have he : 12+(36+states) = 48+states := by omega
  rw [he] at hu
  exact hu

/-- Both sides contain another pair. Exactly one unary token and one payload
marker are changed, with all data and both boundaries restored. -/
theorem both_found (continuation : Nat → Bool → Row) (k : Nat) (tokens : List Bool)
    (xs ys : List Bool) (b c : Bool) (certificate tail : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate k true ++ false::tokens) certificate,
        2*zeros xs (flipped (b::c::ys) tail),some 0⟩ (4*k+6+(4*xs.length+10)) =
    ⟨pairTape (List.replicate k true ++ true::tokens) certificate,
      2*zeros (xs++[b]) (flipped (c::ys) tail),some 48⟩ := by
  unfold table
  rw [run_add,Source284UnaryMarkOne.mark_first]
  change run (Source284UnaryMarkOne.table (Source284MatchDispatch.table continuation))
    (shiftConfig 12 ⟨pairTape (List.replicate k true ++ true::tokens) certificate,
      2*zeros xs (flipped (b::c::ys) tail),some 0⟩) _ = _
  rw [Source284UnaryMarkOne.relocated_run,Source284MatchDispatch.mark _ 0 (by decide)]
  rfl

/-- Unary succeeds but the payload is exhausted; the newly marked unary
token is retained and the corresponding mismatch entry is selected. -/
theorem token_only (continuation : Nat → Bool → Row) (k : Nat) (tokens : List Bool)
    (xs : List Bool) (certificate tail : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate k true ++ false::tokens) certificate,
        2*zeros xs (flipped [false] tail),some 0⟩ (4*k+6+(4*xs.length+10)) =
    ⟨pairTape (List.replicate k true ++ true::tokens) certificate,
      2*zeros xs (flipped [false] tail),some 49⟩ := by
  unfold table
  rw [run_add,Source284UnaryMarkOne.mark_first]
  change run (Source284UnaryMarkOne.table (Source284MatchDispatch.table continuation))
    (shiftConfig 12 ⟨pairTape (List.replicate k true ++ true::tokens) certificate,
      2*zeros xs (flipped [false] tail),some 0⟩) _ = _
  rw [Source284UnaryMarkOne.relocated_run,Source284MatchDispatch.exhausted _ 0 (by decide)]
  rfl

/-- Unary is exhausted but another payload pair exists. Its marker changes,
and the other mismatch continuation is selected. -/
theorem payload_only (continuation : Nat → Bool → Row) (k : Nat)
    (xs ys : List Bool) (b c : Bool) (certificate tail : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate k true) certificate,
        2*zeros xs (flipped (b::c::ys) tail),some 0⟩ (4*k+6+(4*xs.length+10)) =
    ⟨pairTape (List.replicate k true) certificate,
      2*zeros (xs++[b]) (flipped (c::ys) tail),some 50⟩ := by
  unfold table
  rw [run_add,Source284UnaryMarkOne.all_marked]
  change run (Source284UnaryMarkOne.table (Source284MatchDispatch.table continuation))
    (shiftConfig 12 ⟨pairTape (List.replicate k true) certificate,
      2*zeros xs (flipped (b::c::ys) tail),some 1⟩) _ = _
  rw [Source284UnaryMarkOne.relocated_run,Source284MatchDispatch.mark _ 1 (by decide)]
  rfl

/-- Both sides are exhausted; the entire tape is unchanged. -/
theorem both_exhausted (continuation : Nat → Bool → Row) (k : Nat)
    (xs : List Bool) (certificate tail : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate k true) certificate,
        2*zeros xs (flipped [false] tail),some 0⟩ (4*k+6+(4*xs.length+10)) =
    ⟨pairTape (List.replicate k true) certificate,
      2*zeros xs (flipped [false] tail),some 51⟩ := by
  unfold table
  rw [run_add,Source284UnaryMarkOne.all_marked]
  change run (Source284UnaryMarkOne.table (Source284MatchDispatch.table continuation))
    (shiftConfig 12 ⟨pairTape (List.replicate k true) certificate,
      2*zeros xs (flipped [false] tail),some 1⟩) _ = _
  rw [Source284UnaryMarkOne.relocated_run,Source284MatchDispatch.exhausted _ 1 (by decide)]
  rfl

end Shared.Beeping.NPcoNP.Source284MatchStep
