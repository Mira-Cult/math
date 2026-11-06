import Shared.Beeping.NPcoNP.Source284CertificatePrefix
import Shared.ComplexityBridge.Encodings

/-! A five-logical-state, bit-preserving source-table segment for the
canonical Boolean-list witness grammar. State 0 expects a block marker,
state 1 its payload, state 2 its terminating zero, state 3 a blank tail,
and state 4 is a permanent reject sink. A caller must still supply an actual
finite timer, connect the checked prefix, rewind the tape, and link a verifier.
No physical beeper or polynomial reduction is claimed here. -/

namespace Shared.Beeping.NPcoNP.Source284CertificateGrammar

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (run_front)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack stack_cons_mod stack_cons_div)

def next : Nat → Bool → Nat
  | 0, b => if b then 1 else 3
  | 1, _ => 2
  | 2, b => if b then 4 else 0
  | 3, b => if b then 4 else 3
  | _, _ => 4

def scanState : Nat → List Bool → Nat
  | q, [] => q
  | q, b::bs => scanState (next q b) bs

def table (q : Nat) (read : Bool) : Row := ⟨read,false,some (next q read)⟩

theorem next_lt (q : Nat) (b : Bool) : next q b < 5 := by
  cases q with
  | zero => cases b <;> decide
  | succ q =>
    cases q with
    | zero => cases b <;> decide
    | succ q =>
      cases q with
      | zero => cases b <;> decide
      | succ q =>
        cases q with
        | zero => cases b <;> decide
        | succ q => cases b <;> simp [next]

theorem table_closed : Closed 5 table := by
  intro q _ b q' h
  simp only [table, Option.some.injEq] at h
  subst q'
  exact next_lt q b

theorem scan_step (q left tail : Nat) (b : Bool) (rest : List Bool) :
    step table ⟨left,stack (b::rest) tail,some q⟩ =
      ⟨2*left+(if b then 1 else 0),stack rest tail,some (next q b)⟩ := by
  cases b <;> simp [step,table,stack_cons_mod,stack_cons_div,Nat.testBit_zero,bit]

/-- Exactly one relative step per supplied bit; both the scanned bits and the
arbitrary unread high tail remain represented on the two tape halves. -/
theorem scan (bits : List Bool) (q left tail : Nat) :
    run table ⟨left,stack bits tail,some q⟩ bits.length =
      ⟨payloadFold left bits,tail,some (scanState q bits)⟩ := by
  induction bits generalizing q left with
  | nil => simp [run,payloadFold,stack,scanState]
  | cons b bs ih =>
    rw [List.length_cons,run_front,scan_step]
    simpa [payloadFold,scanState] using ih (next q b) (2*left+if b then 1 else 0)

theorem scanState_append (q : Nat) (xs ys : List Bool) :
    scanState q (xs++ys) = scanState (scanState q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih => simpa [scanState] using ih (next q b)

theorem witness_block (b : Bool) : scanState 0 [true,b,false] = 0 := by
  cases b <;> decide

theorem canonical_witness (w : List Bool) :
    scanState 0 (BitstringEncoding.bitEncode w) = 0 := by
  induction w with
  | nil => rfl
  | cons b bs ih =>
    change scanState 0 ([true,b,false] ++ BitstringEncoding.bitEncode bs) = 0
    rw [scanState_append, witness_block]
    exact ih

/-- A finite observation may end after a marker or its payload. These two
states are not rejected; virtual zeros complete the last triple. -/
theorem partial_marker (w : List Bool) :
    scanState 0 (BitstringEncoding.bitEncode w ++ [true]) = 1 := by
  rw [scanState_append,canonical_witness]
  rfl

theorem partial_payload (w : List Bool) (b : Bool) :
    scanState 0 (BitstringEncoding.bitEncode w ++ [true,b]) = 2 := by
  rw [scanState_append,canonical_witness]
  cases b <;> rfl

/-- A one in a triple's mandatory terminator or after the tail delimiter
enters the permanent reject state. -/
theorem bad_terminator (w : List Bool) (b : Bool) :
    scanState 0 (BitstringEncoding.bitEncode w ++ [true,b,true]) = 4 := by
  rw [scanState_append,canonical_witness]
  cases b <;> rfl

theorem bad_tail (w : List Bool) :
    scanState 0 (BitstringEncoding.bitEncode w ++ [false,true]) = 4 := by
  rw [scanState_append,canonical_witness]
  rfl

/-- Once the following virtual or explicit zero is scanned, any number of
additional blank bits leaves the checker in its continuing tail state. -/
theorem canonical_with_blanks (w : List Bool) (n : Nat) :
    scanState 0 (BitstringEncoding.bitEncode w ++ false :: List.replicate n false) = 3 := by
  rw [scanState_append,canonical_witness]
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, scanState, next, Bool.false_eq_true,
      ↓reduceIte] using ih

theorem sink_stable (bits : List Bool) : scanState 4 bits = 4 := by
  induction bits with
  | nil => rfl
  | cons b bs ih => cases b <;> simpa [scanState,next] using ih

theorem source_scan (bits : List Bool) (q left tail codeTail : Nat) (hq : q < 5) :
    Shared.Beeping.NPcoNP.Source284Relative.run (encode 5 table codeTail)
      (toSource ⟨left,stack bits tail,some q⟩) bits.length =
        toSource ⟨payloadFold left bits,tail,some (scanState q bits)⟩ := by
  have hv : Valid 5 ⟨left,stack bits tail,some q⟩ := by
    intro r hr
    simp only [Option.some.injEq] at hr
    omega
  rw [run_toSource 5 table codeTail _ table_closed hv,scan]

end Shared.Beeping.NPcoNP.Source284CertificateGrammar
