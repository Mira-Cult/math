import Shared.Beeping.NPcoNP.Source284ScratchUnaryRunway

/-! A finite source scanner for two-cell unary tokens and the protected
certificate sentinel. Token data may be either bit, permitting later marking.
The scanner requires this representation on tape; no dynamic comparison or
handoff from the continuously running runway is claimed. -/
namespace Shared.Beeping.NPcoNP.Source284UnaryPairScanner

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284PayloadLoop (scratch)
open Shared.Beeping.NPcoNP.Source284ScratchTerminator (mark)
open Shared.Beeping.NPcoNP.Source284ScratchScanner (push)
open Shared.Beeping.NPcoNP.Source284ScratchSentinel (unaryPairs)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

def pairTape (xs : List Bool) (certificate : Nat) : Nat := scratch xs (4*certificate+2)

/-- Turn toward the tokens, then enter the existing marker scanner after its
own initial boundary crossing. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 2⟩
  else shiftRow 1 (Source284ScratchScanner.table continuation (q-1) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (4+states) (table continuation) := by
  have hs := Source284ScratchScanner.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [table] at hnext; omega
  · have ht : (shiftRow 1 (Source284ScratchScanner.table continuation (q-1) b)).next = some q' := by
      simpa [table,h0] using hnext
    have hq0 : q-1 < 3+states := by omega
    cases he : (Source284ScratchScanner.table continuation (q-1) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hs (q-1) hq0 b r he
      simp [shiftRow,he] at ht
      subst q'
      omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (1+q) b = shiftRow 1 (Source284ScratchScanner.table continuation q b) := by
  simp [table]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 1 c) =
      shiftConfig 1 (step (Source284ScratchScanner.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 1 c) fuel =
      shiftConfig 1 (run (Source284ScratchScanner.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem turn (continuation : Nat → Bool → Row) (left right : Nat) :
    step (table continuation) ⟨left,right,some 0⟩ = ⟨right,left,some 2⟩ := by
  simp [step,table,bit,Nat.testBit_zero] <;> split_ifs <;> omega

/-- Every marked or unmarked token is preserved; the `0,1` sentinel ends
the finite scan and the untouched certificate appears under the head. -/
theorem scan (continuation : Nat → Bool → Row) (xs : List Bool) (certificate right : Nat) :
    run (table continuation) ⟨pairTape xs certificate,right,some 0⟩ (2*xs.length+3) =
      ⟨4*push right xs+1,certificate,some 4⟩ := by
  have ht : 2*xs.length+3 = (2*xs.length+2)+1 := by omega
  rw [ht,Source284HardwireTable.run_front,turn]
  change run (table continuation) (shiftConfig 1 ⟨right,pairTape xs certificate,some 1⟩) _ = _
  rw [relocated_run]
  have hm : mark (4*certificate) = 4*certificate+2 := by simp [mark]
  have hd : (4*certificate)/4 = certificate := by omega
  have hs := Source284ScratchScanner.scan continuation xs right (4*certificate)
  rw [hm,hd] at hs
  change run (Source284ScratchScanner.table continuation)
    ⟨right,pairTape xs certificate,some 1⟩ _ = _ at hs
  rw [hs]
  rfl

/-- All-zero tokens are precisely the runway representation produced by the
sentinel construction. -/
theorem zero_pairTape (k certificate : Nat) :
    pairTape (List.replicate k false) certificate =
      Source284LoaderAlgebra.stack (unaryPairs k) certificate := by
  induction k with
  | zero => simp [pairTape,scratch,unaryPairs,Source284LoaderAlgebra.stack] <;> omega
  | succ k ih =>
    simp [pairTape,scratch,unaryPairs,Source284LoaderAlgebra.stack,bit,List.replicate_succ] at *
    omega

theorem push_zeros (k left : Nat) : push left (List.replicate k false) = 4^k*left := by
  induction k generalizing left with
  | zero => simp [push]
  | succ k ih =>
    simp only [List.replicate_succ,push,bit,Bool.false_eq_true,if_false,zero_mul,add_zero,ih,pow_succ]
    ring

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  encode (4+states) (table continuation) 1

/-- The numeric source encoding scans arbitrary token data, not just zeros;
the proof includes the actual turn and preserves the full certificate. -/
theorem source_scan_tokens (states : Nat) (continuation : Nat → Bool → Row)
    (xs : List Bool) (certificate right : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial right (pairTape xs certificate)) (2*xs.length+3) =
      ⟨4*push right xs+1,certificate,active 4⟩ := by
  let c : Config := ⟨pairTape xs certificate,right,some 0⟩
  have hvalid : Valid (4+states) c := by
    intro q hq
    simp [c] at hq
    subst q
    omega
  have hr := run_toSource (4+states) (table continuation) 1 c (closed states continuation hn hv) hvalid (2*xs.length+3)
  change Source284Relative.run (description states continuation)
    (Source284Relative.initial right (pairTape xs certificate)) _ = _ at hr
  rw [hr]
  dsimp only [c]
  rw [scan]
  rfl

/-- The supplied finite continuation executes after the marker scan, with
its subsequent steps charged and relocation recorded. -/
theorem source_after_scan (states : Nat) (continuation : Nat → Bool → Row)
    (xs : List Bool) (certificate right fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    let c : Config := ⟨4*push right xs+1,certificate,some 0⟩
    Source284Relative.run (description states continuation)
      (Source284Relative.initial right (pairTape xs certificate)) (2*xs.length+3+fuel) =
      toSource (shiftConfig 1 (shiftConfig 3 (run continuation c fuel))) := by
  let initial : Config := ⟨pairTape xs certificate,right,some 0⟩
  let c : Config := ⟨4*push right xs+1,certificate,some 0⟩
  have hvalid : Valid (4+states) initial := by
    intro q hq
    simp [initial] at hq
    subst q
    omega
  have hr := run_toSource (4+states) (table continuation) 1 initial (closed states continuation hn hv)
    hvalid (2*xs.length+3+fuel)
  change Source284Relative.run (description states continuation)
    (Source284Relative.initial right (pairTape xs certificate)) _ = _ at hr
  rw [hr,Source284PayloadPop.run_add]
  dsimp only [initial]
  rw [scan]
  change toSource (run (table continuation) (shiftConfig 1 (shiftConfig 3 c)) fuel) = _
  rw [relocated_run,Source284ScratchScanner.relocated_run]

/-- The encoded source table scans a prepared unary runway and reaches the
unchanged certificate in `2*k+3` steps, for arbitrary other tape data. -/
theorem source_scan_runway (states : Nat) (continuation : Nat → Bool → Row)
    (k : Nat) (w : List Bool) (certificate tail : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (2*flipped w tail)
        (Source284LoaderAlgebra.stack (unaryPairs k) certificate)) (2*k+3) =
      ⟨4^(k+1)*(2*flipped w tail)+1,certificate,active 4⟩ := by
  let c : Config := ⟨Source284LoaderAlgebra.stack (unaryPairs k) certificate,2*flipped w tail,some 0⟩
  have hvalid : Valid (4+states) c := by
    intro q hq
    simp [c] at hq
    subst q
    omega
  have hr := run_toSource (4+states) (table continuation) 1 c (closed states continuation hn hv) hvalid (2*k+3)
  change Source284Relative.run (description states continuation)
    (Source284Relative.initial (2*flipped w tail)
      (Source284LoaderAlgebra.stack (unaryPairs k) certificate)) _ = _ at hr
  rw [hr]
  have hs := scan continuation (List.replicate k false) certificate (2*flipped w tail)
  rw [zero_pairTape,push_zeros] at hs
  simp only [List.length_replicate] at hs
  dsimp only [c]
  rw [hs]
  simp [toSource,nextState,active,pow_succ]
  ring

namespace Fixtures
example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 2 481) 7 =
      ⟨161,7,active 4⟩ := by
  simpa [pairTape,scratch,push,bit] using
    source_scan_tokens states continuation [true,false] 7 2 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 22 480) 7 =
      ⟨1409,7,active 4⟩ := by
  simpa [unaryPairs,Source284LoaderAlgebra.stack,flipped,bit] using
    source_scan_runway states continuation 2 [true,false] 7 0 hn hv
end Fixtures

end Shared.Beeping.NPcoNP.Source284UnaryPairScanner
