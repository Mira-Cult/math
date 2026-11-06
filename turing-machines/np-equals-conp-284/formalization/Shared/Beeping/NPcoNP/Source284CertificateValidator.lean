import Shared.Beeping.NPcoNP.Source284CertificateGrammarClock

/-! A finite relative-table prefix and bounded witness-grammar validator. It
scans an explicitly supplied expected prefix followed by exactly `clock`
further bits, preserving the tape bits and retaining the unscanned suffix.
The four nonrejecting grammar modes are exposed as separate boundary states.
Boundary rows currently go to a permanent reject sink: a later construction
must replace them with a paid rewind and verifier continuation. This is not
a polynomial-time generator, a SAT reduction, or a physical beeper proof. -/
namespace Shared.Beeping.NPcoNP.Source284CertificateValidator

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (run_front)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack stack_cons_mod stack_cons_div)
open Shared.Beeping.NPcoNP.Source284CertificatePrefix (stack_append)
open Shared.Beeping.NPcoNP.Source284CertificateGrammar (next next_lt scanState)
open Shared.Beeping.NPcoNP.Source284CertificateGrammarClock (state state_div state_mod)

theorem run_add (t : Nat → Bool → Row) (c : Config) (a b : Nat) :
    run t c (a+b) = run t (run t c a) b := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    change step t (run t c (a+b)) = step t (run t (run t c a) b)
    rw [ih]

def boundary (expected : List Bool) (clock mode : Nat) : Nat :=
  expected.length + state clock mode
def sink (expected : List Bool) (clock : Nat) : Nat := expected.length+5*clock+5
def allocated (expected : List Bool) (clock : Nat) : Nat := sink expected clock+1

def table (expected : List Bool) (clock q : Nat) (read : Bool) : Row :=
  if q < expected.length then
    ⟨read,false,some (if read = (expected[q]?).getD false then q+1 else sink expected clock)⟩
  else if q < expected.length+5*clock then
    ⟨read,false,some (expected.length +
      state ((q-expected.length)/5+1) (next ((q-expected.length)%5) read))⟩
  else ⟨read,false,some (sink expected clock)⟩

theorem prefix_row (expected : List Bool) (clock q : Nat) (b : Bool)
    (hq : q < expected.length) :
    table expected clock q b = ⟨b,false,some
      (if b = (expected[q]?).getD false then q+1 else sink expected clock)⟩ := by
  simp [table,hq]

theorem grammar_row (expected : List Bool) (clock i mode : Nat)
    (hi : i < clock) (hm : mode < 5) (b : Bool) :
    table expected clock (expected.length+state i mode) b =
      ⟨b,false,some (expected.length+state (i+1) (next mode b))⟩ := by
  have hlo : ¬ expected.length+state i mode < expected.length := by omega
  have hhi : expected.length+state i mode < expected.length+5*clock := by
    have h := Shared.Beeping.NPcoNP.Source284CertificateGrammarClock.state_lt clock i mode hi hm
    omega
  simp [table,hlo,hhi,state_div i mode hm,state_mod i mode hm]

theorem closed (expected : List Bool) (clock : Nat) :
    Closed (allocated expected clock) (table expected clock) := by
  intro q hq b q' hnext
  unfold table at hnext
  split_ifs at hnext with hp hg hm
  · simp only [Option.some.injEq] at hnext
    subst q'
    simp only [allocated,sink]
    omega
  · simp only [Option.some.injEq] at hnext
    subst q'
    simp only [allocated,sink]
    omega
  · simp only [Option.some.injEq] at hnext
    subst q'
    have hmode := next_lt ((q-expected.length)%5) b
    have hidx : (q-expected.length)/5 < clock := by omega
    simp [allocated,sink,state]
    omega
  · simp only [Option.some.injEq] at hnext
    subst q'
    simp [allocated]

theorem prefix_step (expected : List Bool) (clock q left tail : Nat)
    (hq : q < expected.length) (b : Bool) (rest : List Bool) :
    step (table expected clock) ⟨left,stack (b::rest) tail,some q⟩ =
      ⟨2*left+(if b then 1 else 0),stack rest tail,
       some (if b = (expected[q]?).getD false then q+1 else sink expected clock)⟩ := by
  cases b <;> simp [step,prefix_row expected clock q _ hq,
    stack_cons_mod,stack_cons_div,Nat.testBit_zero,bit]

theorem prefix_part (before part after : List Bool) (clock left tail : Nat) :
    run (table (before++part++after) clock)
      ⟨left,stack part tail,some before.length⟩ part.length =
      ⟨payloadFold left part,tail,some (before.length+part.length)⟩ := by
  induction part generalizing before left with
  | nil => simp [run,payloadFold,stack]
  | cons b bs ih =>
    have hq : before.length < (before++(b::bs)++after).length := by simp
    have hbit : (((before++(b::bs)++after)[before.length]?).getD false) = b := by
      rw [show before++(b::bs)++after = before++((b::bs)++after) by simp [List.append_assoc]]
      rw [List.getElem?_append_right (by omega)]
      simp
    have hs := prefix_step (before++(b::bs)++after) clock before.length left tail hq b bs
    rw [hbit] at hs
    simp only [↓reduceIte] at hs
    have hn := ih (before++[b]) (2*left+if b then 1 else 0)
    simp only [List.length_append,List.length_singleton] at hn
    rw [List.length_cons,run_front,hs]
    simpa [List.append_assoc,payloadFold,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hn

theorem prefix_scan (expected : List Bool) (clock left tail : Nat) :
    run (table expected clock) ⟨left,stack expected tail,some 0⟩ expected.length =
      ⟨payloadFold left expected,tail,some expected.length⟩ := by
  simpa using prefix_part [] expected [] clock left tail

theorem grammar_step (expected : List Bool) (clock i mode left tail : Nat)
    (hi : i < clock) (hm : mode < 5) (b : Bool) (rest : List Bool) :
    step (table expected clock)
      ⟨left,stack (b::rest) tail,some (expected.length+state i mode)⟩ =
      ⟨2*left+(if b then 1 else 0),stack rest tail,
       some (expected.length+state (i+1) (next mode b))⟩ := by
  cases b <;> simp [step,grammar_row expected clock i mode hi hm,
    stack_cons_mod,stack_cons_div,Nat.testBit_zero,bit]

theorem grammar_scan (expected : List Bool) (clock i mode : Nat) (bits : List Bool)
    (left tail : Nat) (hb : i+bits.length ≤ clock) (hm : mode < 5) :
    run (table expected clock)
      ⟨left,stack bits tail,some (expected.length+state i mode)⟩ bits.length =
      ⟨payloadFold left bits,tail,
        some (expected.length+state (i+bits.length) (scanState mode bits))⟩ := by
  induction bits generalizing i mode left with
  | nil => simp [run,payloadFold,stack,scanState]
  | cons b bs ih =>
    have hi : i < clock := by simp at hb; omega
    have hb' : i+1+bs.length ≤ clock := by simp at hb; omega
    rw [List.length_cons,run_front,grammar_step expected clock i mode left tail hi hm b bs]
    have hh := ih (i+1) (next mode b) (2*left+if b then 1 else 0) hb' (next_lt mode b)
    simpa [payloadFold,scanState,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- The full matching prefix and the next `bits.length` certificate bits are
examined in exactly their combined length, without erasing any high suffix. -/
theorem matching_scan (expected bits : List Bool) (left tail : Nat) :
    run (table expected bits.length)
      ⟨left,stack (expected++bits) tail,some 0⟩ (expected.length+bits.length) =
      ⟨payloadFold (payloadFold left expected) bits,tail,
        some (boundary expected bits.length (scanState 0 bits))⟩ := by
  rw [stack_append,run_add,prefix_scan]
  have h := grammar_scan expected bits.length 0 0 bits (payloadFold left expected) tail
    (by omega) (by omega)
  simpa [state,boundary] using h

/-- A mismatch in the expected prefix reaches the common reject sink at the
very next step; all later input bits are unconstrained. -/
theorem first_mismatch (before after observed : List Bool) (clock : Nat)
    (want actual : Bool) (hbad : actual ≠ want) (left tail : Nat) :
    (run (table (before++want::after) clock)
      ⟨left,stack (before++actual::observed) tail,some 0⟩ (before.length+1)).state =
        some (sink (before++want::after) clock) := by
  have hs := prefix_part [] before (want::after) clock left (stack (actual::observed) tail)
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hs
  rw [stack_append,run,hs]
  have hq : before.length < (before++want::after).length := by simp
  have hbit : (((before++want::after)[before.length]?).getD false) = want := by
    rw [List.getElem?_append_right (by omega)]
    simp
  rw [prefix_step _ _ _ _ _ hq actual observed,hbit]
  simp [hbad]

theorem sink_step (expected : List Bool) (clock left right : Nat) :
    (step (table expected clock) ⟨left,right,some (sink expected clock)⟩).state =
      some (sink expected clock) := by
  have h₁ : ¬ sink expected clock < expected.length := by simp [sink]; omega
  have h₂ : ¬ sink expected clock < expected.length+5*clock := by simp [sink]
  simp [step,table,h₁,h₂]

theorem sink_forever (expected : List Bool) (clock : Nat) (c : Config) (k : Nat)
    (h : c.state = some (sink expected clock)) :
    (run (table expected clock) c k).state = some (sink expected clock) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    cases hc : run (table expected clock) c k with
    | mk left right state =>
      have hs : state = some (sink expected clock) := by simpa [hc] using ih
      subst state
      simpa [run,hc] using sink_step expected clock left right

/-- All modes currently leave the boundary for the sink. A real verifier
must explicitly replace the rows for modes 0 and 3 with its rewind dispatch. -/
theorem boundary_row (expected : List Bool) (clock mode : Nat) (b : Bool) :
    table expected clock (boundary expected clock mode) b =
      ⟨b,false,some (sink expected clock)⟩ := by
  simp [table,boundary,state]

theorem source_matching (expected bits : List Bool) (left tail codeTail : Nat) :
    Shared.Beeping.NPcoNP.Source284Relative.run
      (encode (allocated expected bits.length) (table expected bits.length) codeTail)
      (toSource ⟨left,stack (expected++bits) tail,some 0⟩) (expected.length+bits.length) =
        toSource ⟨payloadFold (payloadFold left expected) bits,tail,
          some (boundary expected bits.length (scanState 0 bits))⟩ := by
  have hv : Valid (allocated expected bits.length)
      ⟨left,stack (expected++bits) tail,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    simp [allocated,sink] at *
    omega
  rw [run_toSource (allocated expected bits.length) (table expected bits.length) codeTail _
    (closed expected bits.length) hv,matching_scan]

end Shared.Beeping.NPcoNP.Source284CertificateValidator
