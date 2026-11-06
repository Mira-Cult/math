import Shared.Beeping.NPcoNP.Source284CertificateValidator
import Shared.Beeping.NPcoNP.Source284WindowRewind

/-! Finite prefix/grammar validation with a real timed rewind dispatch.
At the boundary only complete syntax modes 0 and 3 turn into a shared
preserving rewind; all other modes enter a nonaccepting sink. The rewind
restores the full certificate including any unscanned high tail and exposes
a continuing handoff, not yet a linked verifier. Construction of these rows
in polynomial time and the SAT reduction remain separate obligations. -/
namespace Shared.Beeping.NPcoNP.Source284CertificateDispatch

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (run_front)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack stack_cons_mod stack_cons_div)
open Shared.Beeping.NPcoNP.Source284CertificatePrefix (stack_append)
open Shared.Beeping.NPcoNP.Source284CertificateGrammar (next next_lt scanState)
open Shared.Beeping.NPcoNP.Source284CertificateGrammarClock (state state_div state_mod)
open Shared.Beeping.NPcoNP.Source284CertificateValidator (run_add boundary)

def rewindStart (expected : List Bool) (clock : Nat) : Nat := expected.length+5*clock+5
def width (expected : List Bool) (clock : Nat) : Nat := expected.length+clock
def handoff (expected : List Bool) (clock : Nat) : Nat :=
  rewindStart expected clock + width expected clock + 1
def sink (expected : List Bool) (clock : Nat) : Nat := handoff expected clock + 1
def allocated (expected : List Bool) (clock : Nat) : Nat := sink expected clock + 1

def table (expected : List Bool) (clock q : Nat) (read : Bool) : Row :=
  if q < expected.length then
    ⟨read,false,some (if read = (expected[q]?).getD false then q+1 else sink expected clock)⟩
  else if q < expected.length+5*clock then
    ⟨read,false,some (expected.length +
      state ((q-expected.length)/5+1) (next ((q-expected.length)%5) read))⟩
  else if q = boundary expected clock 0 ∨ q = boundary expected clock 3 then
    ⟨read,true,some (rewindStart expected clock)⟩
  else if rewindStart expected clock ≤ q ∧ q < rewindStart expected clock + width expected clock then
    ⟨read,false,some (q+1)⟩
  else if q = rewindStart expected clock + width expected clock then
    ⟨read,true,some (handoff expected clock)⟩
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

theorem boundary_accept (expected : List Bool) (clock mode : Nat)
    (hm : mode = 0 ∨ mode = 3) (b : Bool) :
    table expected clock (boundary expected clock mode) b =
      ⟨b,true,some (rewindStart expected clock)⟩ := by
  rcases hm with rfl | rfl <;> simp [table,boundary,state]

theorem boundary_reject (expected : List Bool) (clock mode : Nat)
    (hm : mode < 5) (h0 : mode ≠ 0) (h3 : mode ≠ 3) (b : Bool) :
    table expected clock (boundary expected clock mode) b =
      ⟨b,false,some (sink expected clock)⟩ := by
  have hp : ¬ boundary expected clock mode < expected.length := by simp [boundary,state]
  have hg : ¬ boundary expected clock mode < expected.length+5*clock := by simp [boundary,state]
  have hb0 : boundary expected clock mode ≠ boundary expected clock 0 := by simp [boundary,state]; omega
  have hb3 : boundary expected clock mode ≠ boundary expected clock 3 := by simp [boundary,state]; omega
  have hlt : boundary expected clock mode < rewindStart expected clock := by simp [boundary,state,rewindStart]; omega
  have hr : ¬ rewindStart expected clock ≤ boundary expected clock mode := by omega
  have hf : boundary expected clock mode ≠ rewindStart expected clock+width expected clock := by omega
  simp [table,hp,hg,hb0,hb3,hr,hf]

theorem rewind_row (expected : List Bool) (clock i : Nat)
    (hi : i < width expected clock) (b : Bool) :
    table expected clock (rewindStart expected clock+i) b =
      ⟨b,false,some (rewindStart expected clock+i+1)⟩ := by
  have hp : ¬ rewindStart expected clock+i < expected.length := by simp [rewindStart]; omega
  have hg : ¬ rewindStart expected clock+i < expected.length+5*clock := by simp [rewindStart]; omega
  have hb0 : rewindStart expected clock+i ≠ boundary expected clock 0 := by simp [rewindStart,boundary,state]; omega
  have hb3 : rewindStart expected clock+i ≠ boundary expected clock 3 := by simp [rewindStart,boundary,state]; omega
  simp [table,hp,hg,hb0,hb3,hi]

theorem final_turn_row (expected : List Bool) (clock : Nat) (b : Bool) :
    table expected clock (rewindStart expected clock+width expected clock) b =
      ⟨b,true,some (handoff expected clock)⟩ := by
  have hp : ¬ rewindStart expected clock+width expected clock < expected.length := by simp [rewindStart,width]; omega
  have hg : ¬ rewindStart expected clock+width expected clock < expected.length+5*clock := by simp [rewindStart,width]; omega
  have hb0 : rewindStart expected clock+width expected clock ≠ boundary expected clock 0 := by simp [rewindStart,width,boundary,state]; omega
  have hb3 : rewindStart expected clock+width expected clock ≠ boundary expected clock 3 := by simp [rewindStart,width,boundary,state]; omega
  simp [table,hp,hg,hb0,hb3]

theorem closed (expected : List Bool) (clock : Nat) :
    Closed (allocated expected clock) (table expected clock) := by
  intro q hq b q' hnext
  have hm := next_lt ((q-expected.length)%5) b
  unfold table at hnext
  split_ifs at hnext <;> simp_all [allocated,sink,handoff,rewindStart,width,state] <;> omega

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

/-- Prefix and timed grammar scan reach the dispatch mode after exactly
`expected.length+bits.length` steps with the high suffix still present. -/
theorem matching_scan (expected bits : List Bool) (left tail : Nat) :
    run (table expected bits.length)
      ⟨left,stack (expected++bits) tail,some 0⟩ (expected.length+bits.length) =
      ⟨payloadFold (payloadFold left expected) bits,tail,
        some (boundary expected bits.length (scanState 0 bits))⟩ := by
  rw [stack_append,run_add,prefix_scan]
  have h := grammar_scan expected bits.length 0 0 bits (payloadFold left expected) tail
    (by omega) (by omega)
  simpa [state,boundary] using h

theorem sink_row (expected : List Bool) (clock : Nat) (b : Bool) :
    table expected clock (sink expected clock) b = ⟨b,false,some (sink expected clock)⟩ := by
  have hp : ¬ sink expected clock < expected.length := by simp [sink,handoff,rewindStart,width]; omega
  have hg : ¬ sink expected clock < expected.length+5*clock := by simp [sink,handoff,rewindStart,width]; omega
  have hb0 : sink expected clock ≠ boundary expected clock 0 := by simp [sink,handoff,rewindStart,width,boundary,state]; omega
  have hb3 : sink expected clock ≠ boundary expected clock 3 := by simp [sink,handoff,rewindStart,width,boundary,state]; omega
  have hr : ¬ sink expected clock < rewindStart expected clock+width expected clock := by simp [sink,handoff]; omega
  have hf : sink expected clock ≠ rewindStart expected clock+width expected clock := by simp [sink,handoff]; omega
  simp [table,hp,hg,hb0,hb3,hr,hf]

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
      simp [run,hc,step,sink_row]

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

/-- A completed scan in one of the three rejected modes enters the common
permanent sink on the next source transition. -/
theorem rejected_after_scan (expected bits : List Bool) (left tail : Nat)
    (hm : scanState 0 bits < 5)
    (h0 : scanState 0 bits ≠ 0) (h3 : scanState 0 bits ≠ 3) :
    (run (table expected bits.length)
      ⟨left,stack (expected++bits) tail,some 0⟩ (expected.length+bits.length+1)).state =
        some (sink expected bits.length) := by
  rw [run,matching_scan]
  simp [step,boundary_reject expected bits.length (scanState 0 bits) hm h0 h3]

theorem payloadFold_append (left : Nat) (xs ys : List Bool) :
    payloadFold left (xs++ys) = payloadFold (payloadFold left xs) ys := by
  induction xs generalizing left with
  | nil => rfl
  | cons b bs ih => simpa [payloadFold] using ih (2*left+(if b then 1 else 0))

/-- A complete witness mode takes a paid preserving turn, rewinds every
scanned bit, and turns back onto the certificate. The full numeric certificate
is restored, including arbitrary high bits beyond the validated window. -/
theorem matching_rewind (expected bits : List Bool) (tail : Nat)
    (hm : scanState 0 bits = 0 ∨ scanState 0 bits = 3) :
    run (table expected bits.length)
      ⟨0,stack (expected++bits) tail,some 0⟩
      (2*(expected.length+bits.length)+2) =
      ⟨0,stack (expected++bits) tail,some (handoff expected bits.length)⟩ := by
  let allBits := expected++bits
  let q := boundary expected bits.length (scanState 0 bits)
  let start := rewindStart expected bits.length
  have hfirst : ∀ b, table expected bits.length q b = ⟨b,true,some start⟩ := by
    intro b
    exact boundary_accept expected bits.length (scanState 0 bits) hm b
  have hscan : ∀ i < allBits.length, ∀ b,
      table expected bits.length (start+i) b = ⟨b,false,some (start+i+1)⟩ := by
    intro i hi b
    have hi' : i < width expected bits.length := by simpa [allBits,width] using hi
    exact rewind_row expected bits.length i hi' b
  have hlast : ∀ b, table expected bits.length (start+allBits.length) b =
      ⟨b,true,some (start+allBits.length+1)⟩ := by
    intro b
    simpa [allBits,width,handoff,start] using final_turn_row expected bits.length b
  have hr := Shared.Beeping.NPcoNP.Source284WindowRewind.rewind_from_scanned_jump
    (table expected bits.length) q start tail allBits hfirst hscan hlast
  have hlen : allBits.length = expected.length+bits.length := by simp [allBits]
  have htotal : 2*(expected.length+bits.length)+2 =
      (expected.length+bits.length)+(allBits.length+2) := by omega
  rw [htotal,run_add,matching_scan]
  simpa [payloadFold_append,allBits,q,start,handoff,width,hlen] using hr

theorem source_matching_rewind (expected bits : List Bool) (tail codeTail : Nat)
    (hm : scanState 0 bits = 0 ∨ scanState 0 bits = 3) :
    Shared.Beeping.NPcoNP.Source284Relative.run
      (encode (allocated expected bits.length) (table expected bits.length) codeTail)
      (toSource ⟨0,stack (expected++bits) tail,some 0⟩)
      (2*(expected.length+bits.length)+2) =
        toSource ⟨0,stack (expected++bits) tail,some (handoff expected bits.length)⟩ := by
  have hv : Valid (allocated expected bits.length)
      ⟨0,stack (expected++bits) tail,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    simp [allocated,sink,handoff,rewindStart,width] at *
    omega
  rw [run_toSource (allocated expected bits.length) (table expected bits.length) codeTail _
    (closed expected bits.length) hv,matching_rewind expected bits tail hm]

end Shared.Beeping.NPcoNP.Source284CertificateDispatch
