import Shared.Beeping.NPcoNP.Source284HardwireWrite
import Shared.Beeping.NPcoNP.Source284LoaderAlgebra

/-! A bounded prefix-checking segment for a certificate already facing the
source head. This is a concrete finite relative table. It retains every scanned
bit, reaches a continuing boundary on a matching prefix and a nonaccepting
sink on the first mismatch. It neither validates the remaining witness grammar
nor implements the turn, rewind, verifier, serializer, or a complexity result. -/

namespace Shared.Beeping.NPcoNP.Source284CertificatePrefix

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (run_front bit_decide_mod)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack stack_cons_mod stack_cons_div)

def sink (expected : List Bool) : Nat := expected.length + 1

/-- Boundary `expected.length` and sink `expected.length+1` are both continuing;
their rows are deliberately not part of a verifier handoff. -/
def table (expected : List Bool) (q : Nat) (read : Bool) : Row :=
  if q < expected.length then
    ⟨read, false, some (if read = (expected[q]?).getD false then q+1 else sink expected)⟩
  else ⟨read, false, some (sink expected)⟩

theorem table_closed (expected : List Bool) : Closed (expected.length+2) (table expected) := by
  intro q hq read q' hnext
  unfold table at hnext
  split_ifs at hnext <;> simp_all [sink] <;> omega

theorem scan_step (expected : List Bool) (q left tail : Nat)
    (hq : q < expected.length) (b : Bool) (rest : List Bool) :
    step (table expected) ⟨left,stack (b::rest) tail,some q⟩ =
      ⟨2*left + (if b then 1 else 0), stack rest tail,
       some (if b = (expected[q]?).getD false then q+1 else sink expected)⟩ := by
  cases b <;>
    simp [step, table, hq, stack_cons_mod, stack_cons_div, Nat.testBit_zero, bit]

theorem stack_append (xs ys : List Bool) (tail : Nat) :
    stack (xs++ys) tail = stack xs (stack ys tail) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [stack, ih]

/-- A matching finite segment can stop before the rest of the expected word;
the complete unread tape, including an arbitrary suffix, is preserved. -/
theorem scan_matching_part (before part after : List Bool) (left tail : Nat) :
    run (table (before++part++after))
      ⟨left,stack part tail,some before.length⟩ part.length =
      ⟨payloadFold left part,tail,some (before.length+part.length)⟩ := by
  induction part generalizing before left with
  | nil => simp [run, payloadFold, stack]
  | cons b bs ih =>
    have hq : before.length < (before++(b::bs)++after).length := by simp
    have hbit : (((before++(b::bs)++after)[before.length]?).getD false) = b := by
      rw [show before++(b::bs)++after = before++((b::bs)++after) by simp [List.append_assoc]]
      rw [List.getElem?_append_right (by omega)]
      simp
    have hs := scan_step (before++(b::bs)++after) before.length left tail hq b bs
    rw [hbit] at hs
    simp only [↓reduceIte] at hs
    have hn := ih (before++[b]) (2*left + if b then 1 else 0)
    simp only [List.length_append, List.length_singleton] at hn
    rw [List.length_cons, run_front, hs]
    simpa [List.append_assoc, payloadFold, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hn

/-- An exact matching expected is scanned in its length, preserving its bits
on the opposite tape half and retaining any unread higher suffix. -/
theorem scan_matching_suffix (pre rest : List Bool) (left tail : Nat) :
    run (table (pre++rest)) ⟨left,stack rest tail,some pre.length⟩ rest.length =
      ⟨payloadFold left rest,tail,some (pre++rest).length⟩ := by
  induction rest generalizing pre left with
  | nil => simp [run, payloadFold, stack]
  | cons b bs ih =>
    have hq : pre.length < (pre++b::bs).length := by simp
    have hbit : (((pre++b::bs)[pre.length]?).getD false) = b := by
      rw [List.getElem?_append_right (by omega)]
      simp
    have hs := scan_step (pre++b::bs) pre.length left tail hq b bs
    rw [hbit] at hs
    simp only [↓reduceIte] at hs
    have hn := ih (pre++[b]) (2*left + if b then 1 else 0)
    simp only [List.length_append, List.length_singleton] at hn
    rw [List.length_cons, run_front, hs]
    simpa [List.append_assoc, payloadFold, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hn

theorem scan_matching (expected : List Bool) (left tail : Nat) :
    run (table expected) ⟨left,stack expected tail,some 0⟩ expected.length =
      ⟨payloadFold left expected,tail,some expected.length⟩ := by
  simpa using scan_matching_suffix [] expected left tail

/-- A wrong bit after a matching initial segment reaches the reject sink in
exactly one more transition, regardless of all later certificate bits. -/
theorem first_mismatch (before after observed : List Bool)
    (want actual : Bool) (hbad : actual ≠ want) (left tail : Nat) :
    (run (table (before++want::after))
      ⟨left,stack (before++actual::observed) tail,some 0⟩ (before.length+1)).state =
        some (sink (before++want::after)) := by
  have hs := scan_matching_part [] before (want::after) left (stack (actual::observed) tail)
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hs
  have hstack := stack_append before (actual::observed) tail
  rw [hstack, run, hs]
  have hq : before.length < (before++want::after).length := by simp
  have hbit : (((before++want::after)[before.length]?).getD false) = want := by
    rw [List.getElem?_append_right (by omega)]
    simp
  rw [scan_step _ _ _ _ hq actual observed, hbit]
  simp [hbad]

theorem sink_step (expected : List Bool) (left right : Nat) :
    (step (table expected) ⟨left,right,some (sink expected)⟩).state = some (sink expected) := by
  simp [step, table, sink]

theorem sink_forever (expected : List Bool) (c : Config) (k : Nat)
    (h : c.state = some (sink expected)) :
    (run (table expected) c k).state = some (sink expected) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    cases hc : run (table expected) c k with
    | mk left right state =>
      have hs : state = some (sink expected) := by simpa [hc] using ih
      subst state
      simpa [run, hc] using sink_step expected left right

/-- The scanned boundary agrees with the actual unary-record source table;
the code tail and unscanned certificate suffix are arbitrary. -/
theorem source_matching (expected : List Bool) (left tail codeTail : Nat) :
    Shared.Beeping.NPcoNP.Source284Relative.run
      (encode (expected.length+2) (table expected) codeTail)
      (toSource ⟨left,stack expected tail,some 0⟩) expected.length =
      toSource ⟨payloadFold left expected,tail,some expected.length⟩ := by
  have hv : Valid (expected.length+2) ⟨left,stack expected tail,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    omega
  rw [run_toSource (expected.length+2) (table expected) codeTail
    ⟨left,stack expected tail,some 0⟩ (table_closed expected) hv]
  rw [scan_matching]

end Shared.Beeping.NPcoNP.Source284CertificatePrefix
