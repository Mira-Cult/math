import Shared.Beeping.NPcoNP.Source284MatchLoopComplete

/-! Numeric source-table comparison of prepared unary tokens with a
sentinel-framed payload. The table reaches one of three ordered outcomes:
tokens longer, payload longer, or equal. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace Shared.Beeping.NPcoNP.Source284MatchLoopSource

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  encode (48+states) (Source284MatchLoop.table continuation) 1

def compareCost (n : Nat) : Nat := 4*n*n+20*n+16

theorem source_run (states : Nat) (continuation : Nat → Bool → Row)
    (left right clock : Nat) (hn : 4 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial right left) clock =
      toSource (run (Source284MatchLoop.table continuation) ⟨left,right,some 0⟩ clock) := by
  let c : Config := ⟨left,right,some 0⟩
  have hc : Valid (48+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have h := run_toSource (48+states) (Source284MatchLoop.table continuation) 1 c
    (Source284MatchLoop.closed states continuation hn hv) hc clock
  exact h

theorem equal_length (states : Nat) (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) (hn : 4 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (2*flipped (w++[false]) tail) (pairTape (List.replicate w.length false) certificate))
      (compareCost w.length) =
    ⟨pairTape (List.replicate w.length true) certificate,2*zeros w (flipped [false] tail),active 50⟩ := by
  rw [source_run states continuation _ _ _ hn hv]
  change toSource (run (Source284MatchLoop.table continuation) _ (4*w.length*w.length+20*w.length+16)) = _
  rw [Source284MatchLoopComplete.equal_length]
  rfl

theorem more_tokens (states : Nat) (continuation : Nat → Bool → Row) (w : List Bool) (extra : Nat)
    (certificate tail : Nat) (hn : 4 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (2*flipped (w++[false]) tail)
        (pairTape (List.replicate (w.length+1+extra) false) certificate)) (compareCost w.length) =
    ⟨pairTape (List.replicate w.length true ++ true::List.replicate extra false) certificate,
      2*zeros w (flipped [false] tail),active 48⟩ := by
  rw [source_run states continuation _ _ _ hn hv]
  change toSource (run (Source284MatchLoop.table continuation) _ (4*w.length*w.length+20*w.length+16)) = _
  rw [Source284MatchLoopComplete.more_tokens]
  rfl

theorem more_payload (states : Nat) (continuation : Nat → Bool → Row) (w rest : List Bool) (b : Bool)
    (certificate tail : Nat) (hn : 4 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (2*flipped ((w++b::rest)++[false]) tail)
        (pairTape (List.replicate w.length false) certificate)) (compareCost w.length) =
    ⟨pairTape (List.replicate w.length true) certificate,
      2*zeros (w++[b]) (flipped (rest++[false]) tail),active 49⟩ := by
  rw [source_run states continuation _ _ _ hn hv]
  change toSource (run (Source284MatchLoop.table continuation) _ (4*w.length*w.length+20*w.length+16)) = _
  rw [Source284MatchLoopComplete.more_payload]
  rfl

/-- Every prepared all-zero unary tape and sentinel-framed payload reaches a
correctly classified continuation after a quadratic number of source steps. -/
theorem total_compare (states : Nat) (continuation : Nat → Bool → Row) (tokens : Nat) (w : List Bool)
    (certificate tail : Nat) (hn : 4 ≤ states) (hv : Closed states continuation) :
    ∃ left right mode,
      Source284Relative.run (description states continuation)
        (Source284Relative.initial (2*flipped (w++[false]) tail) (pairTape (List.replicate tokens false) certificate))
        (compareCost (min tokens w.length)) = ⟨left,right,active (48+mode)⟩ ∧
      (mode = 0 ↔ w.length < tokens) ∧ (mode = 1 ↔ tokens < w.length) ∧ (mode = 2 ↔ tokens = w.length) := by
  rcases Nat.lt_trichotomy tokens w.length with hlt | heq | hgt
  · have hdlen : 0 < (w.drop tokens).length := by simp; omega
    cases hd : w.drop tokens with
    | nil => simp [hd] at hdlen
    | cons b rest =>
      have hw : w = w.take tokens ++ b::rest := by
        have h := List.take_append_drop tokens w
        rw [hd] at h
        exact h.symm
      have hlen : (w.take tokens).length = tokens := by
        simp [List.length_take,Nat.min_eq_left (by omega : tokens ≤ w.length)]
      let pref := w.take tokens
      have hp := more_payload states continuation pref rest b certificate tail hn hv
      have hprefix : pref.length = tokens := hlen
      rw [hprefix,← hw] at hp
      refine ⟨pairTape (List.replicate tokens true) certificate,
        2*zeros (pref++[b]) (flipped (rest++[false]) tail),1,?_,?_,?_,?_⟩
      · simpa [Nat.min_eq_left (by omega : tokens ≤ w.length)] using hp
      · simp; omega
      · simp [hlt]
      · simp; omega
  · subst tokens
    refine ⟨pairTape (List.replicate w.length true) certificate,
      2*zeros w (flipped [false] tail),2,?_,?_,?_,?_⟩
    · simpa using equal_length states continuation w certificate tail hn hv
    · simp
    · simp
    · simp
  · let extra := tokens-(w.length+1)
    have he : w.length+1+extra = tokens := by dsimp [extra]; omega
    have hp := more_tokens states continuation w extra certificate tail hn hv
    rw [he] at hp
    refine ⟨pairTape (List.replicate w.length true ++ true::List.replicate extra false) certificate,
      2*zeros w (flipped [false] tail),0,?_,?_,?_,?_⟩
    · simpa [Nat.min_eq_right (by omega : w.length ≤ tokens)] using hp
    · simp [hgt]
    · simp; omega
    · simp; omega

/-- Continuation execution is part of the same finite numeric source table. -/
theorem source_after (states : Nat) (continuation : Nat → Bool → Row) (mode : Nat)
    (left right clock : Nat) (hn : 4 ≤ states) (hm : mode < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) ⟨left,right,active (48+mode)⟩ clock =
      toSource (shiftConfig 48 (run continuation ⟨left,right,some mode⟩ clock)) := by
  let c : Config := ⟨left,right,some mode⟩
  have hc : Valid (48+states) (shiftConfig 48 c) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := run_toSource (48+states) (Source284MatchLoop.table continuation) 1
    (shiftConfig 48 c) (Source284MatchLoop.closed states continuation hn hv) hc clock
  change Source284Relative.run (description states continuation) ⟨left,right,active (48+mode)⟩ clock = _ at hr
  rw [hr,Source284MatchLoop.relocated_run]

namespace Fixtures
example (states : Nat) (continuation : Nat → Bool → Row) (hn : 4 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 4 30) 16 =
      ⟨30,4,active 50⟩ := by
  simpa [pairTape,Source284PayloadLoop.scratch,zeros,flipped,bit,compareCost] using
    equal_length states continuation [] 7 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 4 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 86 480) 72 =
      ⟨485,66,active 50⟩ := by
  simpa [pairTape,Source284PayloadLoop.scratch,zeros,flipped,bit,compareCost] using
    equal_length states continuation [true,false] 7 0 hn hv
example (states : Nat) (continuation : Nat → Bool → Row) (hn : 4 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 86 1920) 72 =
      ⟨1941,66,active 48⟩ := by
  simpa [pairTape,Source284PayloadLoop.scratch,zeros,flipped,bit,compareCost] using
    more_tokens states continuation [true,false] 0 7 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 4 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 86 120) 40 =
      ⟨121,66,active 49⟩ := by
  simpa [pairTape,Source284PayloadLoop.scratch,zeros,flipped,bit,compareCost] using
    more_payload states continuation [true] [] false 7 0 hn hv

end Fixtures

end Shared.Beeping.NPcoNP.Source284MatchLoopSource
