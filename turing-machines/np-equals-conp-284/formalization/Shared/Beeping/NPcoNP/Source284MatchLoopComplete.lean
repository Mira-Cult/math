import Shared.Beeping.NPcoNP.Source284MatchLoop

/-! Quantitative iteration and terminal cases of the prepared-tape paired
comparison. Both markers must start with equally long marked prefixes. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace Shared.Beeping.NPcoNP.Source284MatchLoopComplete

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284MatchLoop (table)

theorem both_step_rest (continuation : Nat → Bool → Row) (k : Nat) (tokens : List Bool)
    (xs rest : List Bool) (b : Bool) (certificate tail : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate k true ++ false::tokens) certificate,
        2*zeros xs (flipped ((b::rest)++[false]) tail),some 0⟩ (4*k+6+(4*xs.length+10)) =
    ⟨pairTape (List.replicate k true ++ true::tokens) certificate,
      2*zeros (xs++[b]) (flipped (rest++[false]) tail),some 0⟩ := by
  cases rest with
  | nil => simpa using Source284MatchLoop.both_step continuation k tokens xs [] b false certificate tail
  | cons c ys =>
    simpa using Source284MatchLoop.both_step continuation k tokens xs (ys++[false]) b c certificate tail

def repeatCost (k n : Nat) : Nat := n*(8*k+12+4*n)

theorem repeatCost_zero (k : Nat) : repeatCost k 0 = 0 := by simp [repeatCost]
theorem repeatCost_succ (k n : Nat) : repeatCost k (n+1) = 8*k+16+repeatCost (k+1) n := by
  unfold repeatCost
  ring

theorem replicate_mark (k : Nat) (xs : List Bool) :
    List.replicate k true ++ true::xs = List.replicate (k+1) true ++ xs := by
  rw [Source284UnaryMarkOne.replicate_snoc]
  simp [List.append_assoc]

/-- One table executes all pairwise matches, without any externally supplied
stop signal; `ys` is a proof description of the initial tape. -/
theorem repeat_pairs (continuation : Nat → Bool → Row) (k : Nat) (tokens xs ys rest : List Bool)
    (certificate tail : Nat) (hx : xs.length = k) :
    run (table continuation)
      ⟨pairTape (List.replicate k true ++ List.replicate ys.length false ++ tokens) certificate,
        2*zeros xs (flipped (ys++rest++[false]) tail),some 0⟩ (repeatCost k ys.length) =
    ⟨pairTape (List.replicate (k+ys.length) true ++ tokens) certificate,
      2*zeros (xs++ys) (flipped (rest++[false]) tail),some 0⟩ := by
  induction ys generalizing k xs with
  | nil => simp [repeatCost,run]
  | cons b ys ih =>
    have ht : repeatCost k (b::ys).length =
        (4*k+6+(4*xs.length+10))+repeatCost (k+1) ys.length := by
      simp only [List.length_cons]
      rw [repeatCost_succ]
      rw [hx]
      omega
    rw [ht,run_add]
    simp only [List.length_cons,List.replicate_succ,List.cons_append,List.append_assoc]
    have hs := both_step_rest continuation k (List.replicate ys.length false ++ tokens)
      xs (ys++rest) b certificate tail
    simp only [List.cons_append,List.append_assoc] at hs
    rw [hs]
    rw [replicate_mark]
    have hx' : (xs++[b]).length = k+1 := by simp [hx]
    have hi := ih (k+1) (xs++[b]) hx'
    simp only [List.append_assoc] at hi
    rw [hi]
    simp [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem terminalCost (n : Nat) :
    4*n*n+20*n+16 = repeatCost 0 n + (4*n+6+(4*n+10)) := by
  unfold repeatCost
  ring

/-- Exactly as many zero tokens as payload bits: the comparator reaches the
joint-exhaustion continuation after marking all pairs. -/
theorem equal_length (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) :
    run (table continuation) ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) tail,some 0⟩ (4*w.length*w.length+20*w.length+16) =
    ⟨pairTape (List.replicate w.length true) certificate,
      2*zeros w (flipped [false] tail),some 50⟩ := by
  have hp := repeat_pairs continuation 0 [] [] w [] certificate tail (by rfl)
  simp only [List.length_nil,List.replicate_zero,List.nil_append,List.append_nil,zeros,Nat.zero_add] at hp
  rw [terminalCost,run_add,hp,Source284MatchLoop.exhausted_step]

/-- With one or more extra tokens, the next token is marked and the payload
is exhausted; the mismatch continuation is selected. -/
theorem more_tokens (continuation : Nat → Bool → Row) (w : List Bool) (extra : Nat)
    (certificate tail : Nat) :
    run (table continuation) ⟨pairTape (List.replicate (w.length+1+extra) false) certificate,
      2*flipped (w++[false]) tail,some 0⟩ (4*w.length*w.length+20*w.length+16) =
    ⟨pairTape (List.replicate w.length true ++ true::List.replicate extra false) certificate,
      2*zeros w (flipped [false] tail),some 48⟩ := by
  have hp := repeat_pairs continuation 0 (false::List.replicate extra false) [] w [] certificate tail (by rfl)
  simp only [List.length_nil,List.replicate_zero,List.nil_append,List.append_nil,zeros,Nat.zero_add] at hp
  have he : List.replicate w.length false ++ false::List.replicate extra false =
      List.replicate (w.length+1+extra) false := by
    rw [List.replicate_add,List.replicate_add]
    simp [List.append_assoc]
  rw [he] at hp
  rw [terminalCost,run_add,hp,Source284MatchLoop.token_step]

theorem payload_step_rest (continuation : Nat → Bool → Row) (k : Nat)
    (xs rest : List Bool) (b : Bool) (certificate tail : Nat) :
    run (table continuation) ⟨pairTape (List.replicate k true) certificate,
      2*zeros xs (flipped ((b::rest)++[false]) tail),some 0⟩ (4*k+6+(4*xs.length+10)) =
    ⟨pairTape (List.replicate k true) certificate,
      2*zeros (xs++[b]) (flipped (rest++[false]) tail),some 49⟩ := by
  cases rest with
  | nil => simpa using Source284MatchLoop.payload_step continuation k xs [] b false certificate tail
  | cons c ys =>
    simpa using Source284MatchLoop.payload_step continuation k xs (ys++[false]) b c certificate tail

/-- With additional payload, the next payload marker is changed, and the
opposite mismatch continuation is selected. -/
theorem more_payload (continuation : Nat → Bool → Row) (w rest : List Bool) (b : Bool)
    (certificate tail : Nat) :
    run (table continuation) ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped ((w++b::rest)++[false]) tail,some 0⟩ (4*w.length*w.length+20*w.length+16) =
    ⟨pairTape (List.replicate w.length true) certificate,
      2*zeros (w++[b]) (flipped (rest++[false]) tail),some 49⟩ := by
  have hp := repeat_pairs continuation 0 [] [] w (b::rest) certificate tail (by rfl)
  simp only [List.length_nil,List.replicate_zero,List.nil_append,List.append_nil,zeros,Nat.zero_add] at hp
  rw [terminalCost,run_add,hp,payload_step_rest]

end Shared.Beeping.NPcoNP.Source284MatchLoopComplete
