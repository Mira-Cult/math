import Shared.Beeping.NPcoNP.Source284SingleTaggedDispatch
import Shared.Beeping.NPcoNP.Source284UnaryPairScanner

/-! Convert the delimiter-protected zero gap into the unary bound required
by the tagged witness comparator. This is a finite source table with a
linear paid clock, not yet the raw-input initializer or verifier handoff. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284GapUnaryPrepare

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284SingleTaggedDispatch (boundary)

/-- States 2 and 3 track parity while scanning the gap. State 5 writes a
new sentinel into the last gap cell in the odd case. State 4 returns to and
clears the near delimiter. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨b,b,some (if b then 4 else 3)⟩
  else if q = 3 then ⟨b,b,some (if b then 5 else 2)⟩
  else if q = 4 then ⟨false,false,some (if b then 6 else 4)⟩
  else if q = 5 then ⟨true,false,some 4⟩
  else shiftRow 6 (continuation (q-6) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (6+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases h : q < 6
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 6 (continuation (q-6) b)).next = some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,
        show q ≠ 2 by omega,show q ≠ 3 by omega,
        show q ≠ 4 by omega,show q ≠ 5 by omega] using hnext
    cases hnxt : (continuation (q-6) b).next with
    | none => simp [shiftRow,hnxt] at he
    | some r =>
      have hr := hv (q-6) (by omega) b r hnxt
      simp [shiftRow,hnxt] at he
      subst q'
      omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (6+q) b = shiftRow 6 (continuation q b) := by
  simp [table,show 6+q ≠ 1 by omega,show 6+q ≠ 2 by omega,
    show 6+q ≠ 3 by omega,show 6+q ≠ 4 by omega,show 6+q ≠ 5 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 6 c) = shiftConfig 6 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 6 c) fuel = shiftConfig 6 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

/-- Traverse an even number of zero cells while preserving both halves. -/
theorem forward_pairs (continuation : Nat → Bool → Row) (n left right : Nat) :
    run (table continuation) ⟨left,2^(2*n)*right,some 2⟩ (2*n) =
      ⟨2^(2*n)*left,right,some 2⟩ := by
  induction n generalizing left with
  | zero => simp [run]
  | succ n ih =>
    have hp : 2^(2*(n+1)) = 4*2^(2*n) := by
      rw [show 2*(n+1)=2*n+2 by omega,pow_add]; norm_num; ring
    have ht : 2*(n+1) = 2+2*n := by omega
    rw [hp,ht,Source284ScratchScanner.run_add]
    have h2 (a b : Nat) : step (table continuation) ⟨a,2*b,some 2⟩ =
        ⟨2*a,b,some 3⟩ := by simp [step,table,bit,Nat.testBit_zero]
    have h3 (a b : Nat) : step (table continuation) ⟨a,2*b,some 3⟩ =
        ⟨2*a,b,some 2⟩ := by simp [step,table,bit,Nat.testBit_zero]
    have hs : run (table continuation) ⟨left,4*(2^(2*n)*right),some 2⟩ 2 =
        ⟨4*left,2^(2*n)*right,some 2⟩ := by
      rw [show 4*(2^(2*n)*right)=2*(2*(2^(2*n)*right)) by ring]
      simp only [run,h2,h3]
      congr 1 <;> ring
    rw [show 4*2^(2*n)*right = 4*(2^(2*n)*right) by ring]
    rw [hs,ih]
    congr 1 <;> ring

/-- Return across an arbitrary finite zero run without inspecting the
protected witness or any high input suffix. -/
theorem return_zeros (continuation : Nat → Bool → Row) (n left right : Nat) :
    run (table continuation) ⟨left,2^n*right,some 4⟩ n =
      ⟨2^n*left,right,some 4⟩ := by
  induction n generalizing left with
  | zero => simp [run]
  | succ n ih =>
    rw [pow_succ]
    have he : (2^n*2)*right = 2*(2^n*right) := by ring
    rw [he,run_front]
    have hs : step (table continuation) ⟨left,2*(2^n*right),some 4⟩ =
        ⟨2*left,2^n*right,some 4⟩ := by
      simp [step,table,bit,Nat.testBit_zero]
    rw [hs,ih]
    congr 1 <;> ring

theorem pairTape_zeros (n certificate : Nat) :
    pairTape (List.replicate n false) certificate = 2^(2*n+1)*(2*certificate+1) := by
  rw [Source284UnaryPairScanner.zero_pairTape,Source284ScratchSentinel.unaryPairs_stack,pow_succ]
  ring

theorem start (continuation : Nat → Bool → Row) (gap certificate stream : Nat) :
    run (table continuation) ⟨boundary gap stream,certificate,some 0⟩ 2 =
      ⟨2*certificate+1,2^gap*(2*stream+1),some 2⟩ := by
  have h0 (left right : Nat) : step (table continuation) ⟨left,right,some 0⟩ =
      ⟨right,left,some 1⟩ := by
    simp [step,table,bit,Nat.testBit_zero] <;> split_ifs <;> omega
  have h1 (left right : Nat) : step (table continuation) ⟨left,2*right+1,some 1⟩ =
      ⟨2*left+1,right,some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  simp only [run,h0,boundary,h1]

theorem even_gap (continuation : Nat → Bool → Row) (n certificate stream : Nat) :
    run (table continuation) ⟨boundary (2*n) stream,certificate,some 0⟩ (2*(2*n)+4) =
      ⟨pairTape (List.replicate n false) stream,certificate,some 6⟩ := by
  have hturn (left right : Nat) : step (table continuation) ⟨left,2*right+1,some 2⟩ =
      ⟨2*right+1,left,some 4⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have hclear (left right : Nat) : step (table continuation) ⟨left,2*right+1,some 4⟩ =
      ⟨2*left,right,some 6⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have ht : 2*(2*n)+4 = 2+(2*n+(1+(2*n+1))) := by omega
  rw [ht,Source284ScratchScanner.run_add,start,Source284ScratchScanner.run_add,forward_pairs,
    Source284ScratchScanner.run_add]
  change run (table continuation) (step (table continuation) ⟨_,_,some 2⟩) _ = _
  rw [hturn,Source284ScratchScanner.run_add,return_zeros]
  change step (table continuation) ⟨_,_,some 4⟩ = _
  rw [hclear,pairTape_zeros,pow_succ]
  congr 1 <;> ring

theorem odd_gap (continuation : Nat → Bool → Row) (n certificate stream : Nat) :
    run (table continuation) ⟨boundary (2*n+1) stream,certificate,some 0⟩ (2*(2*n+1)+4) =
      ⟨pairTape (List.replicate n false) (2*stream+1),certificate,some 6⟩ := by
  have h2 (left right : Nat) : step (table continuation) ⟨left,2*right,some 2⟩ =
      ⟨2*left,right,some 3⟩ := by simp [step,table,bit,Nat.testBit_zero]
  have h3 (left right : Nat) : step (table continuation) ⟨left,2*right+1,some 3⟩ =
      ⟨2*right+1,left,some 5⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h5 (left right : Nat) : step (table continuation) ⟨left,2*right,some 5⟩ =
      ⟨2*left+1,right,some 4⟩ := by simp [step,table,bit,Nat.testBit_zero]
  have hclear (left right : Nat) : step (table continuation) ⟨left,2*right+1,some 4⟩ =
      ⟨2*left,right,some 6⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have ht : 2*(2*n+1)+4 = 2+(2*n+(3+(2*n+1))) := by omega
  rw [ht,Source284ScratchScanner.run_add,start]
  have hp : 2^(2*n+1)*(2*stream+1) = 2^(2*n)*(2*(2*stream+1)) := by
    rw [pow_succ]; ring
  rw [hp,Source284ScratchScanner.run_add,forward_pairs,Source284ScratchScanner.run_add]
  simp only [run,h2,h3,h5] at *
  rw [return_zeros]
  change step (table continuation) ⟨_,_,some 4⟩ = _
  rw [hclear,pairTape_zeros,pow_succ]
  congr 1 <;> ring

/-- The original protected stream is retained exactly. When the gap is odd,
the old far delimiter becomes part of the retained suffix and the preceding
zero is rewritten as the new sentinel. -/
def retained (gap stream : Nat) : Nat :=
  if gap%2=0 then stream else 2*stream+1

theorem prepare (continuation : Nat → Bool → Row) (gap certificate stream : Nat) :
    run (table continuation) ⟨boundary gap stream,certificate,some 0⟩ (2*gap+4) =
      ⟨pairTape (List.replicate (gap/2) false) (retained gap stream),certificate,some 6⟩ := by
  by_cases he : gap%2=0
  · let n := gap/2
    have hg : gap=2*n := by dsimp [n]; omega
    have h := even_gap continuation n certificate stream
    rw [← hg] at h
    simpa [retained,he,n] using h
  · let n := gap/2
    have hg : gap=2*n+1 := by dsimp [n]; omega
    have h := odd_gap continuation n certificate stream
    rw [← hg] at h
    simpa [retained,he,n] using h

/-- After the linear preparation, the actual finite table runs the supplied
continuation on the untouched complete certificate and the prepared bound. -/
theorem prepare_then (continuation : Nat → Bool → Row) (gap certificate stream fuel : Nat) :
    run (table continuation) ⟨boundary gap stream,certificate,some 0⟩ (2*gap+4+fuel) =
      shiftConfig 6 (run continuation
        ⟨pairTape (List.replicate (gap/2) false) (retained gap stream),certificate,some 0⟩ fuel) := by
  rw [Source284ScratchScanner.run_add,prepare]
  simpa [shiftConfig] using relocated_run continuation
    ⟨pairTape (List.replicate (gap/2) false) (retained gap stream),certificate,some 0⟩ fuel

/-- The source's numeric table encoding performs the same paid preparation. -/
theorem encoded_prepare (states : Nat) (continuation : Nat → Bool → Row)
    (gap certificate stream fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (6+states) (table continuation) 1)
      (Source284Relative.initial certificate (boundary gap stream)) (2*gap+4+fuel) =
      toSource (shiftConfig 6 (run continuation
        ⟨pairTape (List.replicate (gap/2) false) (retained gap stream),certificate,some 0⟩ fuel)) := by
  let c : Config := ⟨boundary gap stream,certificate,some 0⟩
  have hvalid : Valid (6+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have h := run_toSource (6+states) (table continuation) 1 c (closed states continuation hn hv)
    hvalid (2*gap+4+fuel)
  rw [prepare_then] at h
  exact h

namespace Fixtures
def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩

/-- Zero, odd, and even gaps preserve the original certificate. -/
example : run (table loop) ⟨boundary 0 3,27,some 0⟩ 4 = ⟨14,27,some 6⟩ := by decide +kernel
example : run (table loop) ⟨boundary 1 3,27,some 0⟩ 6 = ⟨30,27,some 6⟩ := by decide +kernel
example : run (table loop) ⟨boundary 2 3,27,some 0⟩ 8 = ⟨56,27,some 6⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284GapUnaryPrepare
