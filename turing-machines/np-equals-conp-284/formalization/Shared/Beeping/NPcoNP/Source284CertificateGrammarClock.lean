import Shared.Beeping.NPcoNP.Source284CertificateGrammar

/-! A finite unrolled clock for the five-state certificate grammar scan.
Each logical state records a consumed-bit count and grammar mode. After the
specified number of steps, the timed boundary is exposed; its rows are not
yet a rewind or verifier handoff. The table is a mathematical finite table,
not a polynomial-time table generator or a complete reduction. -/

namespace Shared.Beeping.NPcoNP.Source284CertificateGrammarClock

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (run_front)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack stack_cons_mod stack_cons_div)
open Shared.Beeping.NPcoNP.Source284CertificateGrammar (next scanState next_lt)

def state (i mode : Nat) : Nat := 5*i+mode
def sink (clock : Nat) : Nat := 5*clock+5
def allocated (clock : Nat) : Nat := 5*clock+6

def table (clock q : Nat) (read : Bool) : Row :=
  if q < 5*clock then
    ⟨read,false,some (state (q/5+1) (next (q%5) read))⟩
  else ⟨read,false,some (sink clock)⟩

theorem state_lt (clock i mode : Nat) (hi : i < clock) (hm : mode < 5) :
    state i mode < 5*clock := by simp [state]; omega

theorem state_div (i mode : Nat) (hm : mode < 5) : state i mode / 5 = i := by
  simp only [state]
  omega

theorem state_mod (i mode : Nat) (hm : mode < 5) : state i mode % 5 = mode := by
  simp [state, Nat.add_mod, Nat.mod_eq_of_lt hm]

theorem active_row (clock i mode : Nat) (hi : i < clock) (hm : mode < 5) (b : Bool) :
    table clock (state i mode) b = ⟨b,false,some (state (i+1) (next mode b))⟩ := by
  simp [table,state_lt clock i mode hi hm,state_div i mode hm,state_mod i mode hm]

theorem table_closed (clock : Nat) : Closed (allocated clock) (table clock) := by
  intro q hq b q' hnext
  unfold table at hnext
  split_ifs at hnext with h
  · simp only [Option.some.injEq] at hnext
    subst q'
    have hm := next_lt (q%5) b
    have hi : q/5 < clock := by omega
    simp [allocated,state]
    omega
  · simp only [Option.some.injEq] at hnext
    subst q'
    simp [allocated,sink]

theorem scan_step (clock i mode left tail : Nat) (hi : i < clock) (hm : mode < 5)
    (b : Bool) (rest : List Bool) :
    step (table clock) ⟨left,stack (b::rest) tail,some (state i mode)⟩ =
      ⟨2*left+(if b then 1 else 0),stack rest tail,some (state (i+1) (next mode b))⟩ := by
  cases b <;> simp [step,active_row clock i mode hi hm,stack_cons_mod,
    stack_cons_div,Nat.testBit_zero,bit]

/-- The unrolled table performs exactly one step per bit until the caller's
paid clock boundary, preserving the scanned and unread tape halves. -/
theorem scan (clock i mode : Nat) (bits : List Bool) (left tail : Nat)
    (hb : i+bits.length ≤ clock) (hm : mode < 5) :
    run (table clock) ⟨left,stack bits tail,some (state i mode)⟩ bits.length =
      ⟨payloadFold left bits,tail,some (state (i+bits.length) (scanState mode bits))⟩ := by
  induction bits generalizing i mode left with
  | nil => simp [run,payloadFold,stack,scanState]
  | cons b bs ih =>
    have hi : i < clock := by simp at hb; omega
    have hb' : i+1+bs.length ≤ clock := by simp at hb; omega
    rw [List.length_cons,run_front,scan_step clock i mode left tail hi hm b bs]
    have hh := ih (i+1) (next mode b) (2*left+if b then 1 else 0) hb' (next_lt mode b)
    simpa [payloadFold,scanState,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- The reject mode cannot be cleared by later input before the timed boundary. -/
theorem reject_stable (clock i : Nat) (bits : List Bool) (left tail : Nat)
    (hb : i+bits.length ≤ clock) :
    (run (table clock) ⟨left,stack bits tail,some (state i 4)⟩ bits.length).state =
      some (state (i+bits.length) 4) := by
  rw [scan clock i 4 bits left tail hb (by omega)]
  simp [Shared.Beeping.NPcoNP.Source284CertificateGrammar.sink_stable]

/-- Exact source encoding lift. `bits.length` must equal the declared clock;
the head begins in mode zero facing the supplied certificate window. -/
theorem source_scan (bits : List Bool) (left tail codeTail : Nat) :
    Shared.Beeping.NPcoNP.Source284Relative.run
      (encode (allocated bits.length) (table bits.length) codeTail)
      (toSource ⟨left,stack bits tail,some (state 0 0)⟩) bits.length =
        toSource ⟨payloadFold left bits,tail,some (state bits.length (scanState 0 bits))⟩ := by
  have hv : Valid (allocated bits.length) ⟨left,stack bits tail,some (state 0 0)⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    simp [allocated,state] at *
    omega
  rw [run_toSource (allocated bits.length) (table bits.length) codeTail _
    (table_closed bits.length) hv]
  rw [scan bits.length 0 0 bits left tail (by omega) (by omega)]
  simp

end Shared.Beeping.NPcoNP.Source284CertificateGrammarClock
