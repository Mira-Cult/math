import Shared.Beeping.NPcoNP.Source284TableRun
import Mathlib.Data.Nat.Pairing

/-! A finite countdown product for a source-relative transition table. The
guard remembers elapsed time in its finite control and redirects nonaccepting
continuations at the supplied cutoff into a permanent nonaccepting sink.
The accepting transition still performs the original write and move. This
module concerns a supplied finite table and a supplied natural cutoff; it
does not assert an effective table serializer or a polynomial-time compiler.
-/
namespace Shared.Beeping.NPcoNP.Source284TableCountdown

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun

/-- For zero clock, logical state zero itself is the rejecting sink. -/
def sink (n cutoff : Nat) : Nat := if cutoff = 0 then 0 else Nat.pair cutoff n

/-- A sufficient finite state bound; no minimality is claimed. -/
def allocated (n cutoff : Nat) : Nat := sink n cutoff + 1

def sinkRow (n cutoff : Nat) (read : Bool) : Row :=
  ⟨read, false, some (sink n cutoff)⟩

/-- Live states encode `(elapsed, original state)`. Invalid product states
and continuations beyond the original table are sent to the reject sink. -/
def table (n cutoff : Nat) (original : Nat → Bool → Row) (s : Nat) (read : Bool) : Row :=
  if s = sink n cutoff then sinkRow n cutoff read
  else
    let p := Nat.unpair s
    if p.1 < cutoff ∧ p.2 < n then
      let r := original p.2 read
      ⟨r.write, r.turn,
        match r.next with
        | none => none
        | some q => if p.1 + 1 < cutoff ∧ q < n then
            some (Nat.pair (p.1+1) q) else some (sink n cutoff)⟩
    else sinkRow n cutoff read

def mapped (n cutoff elapsed : Nat) (c : Config) : Config :=
  ⟨c.left, c.right,
    c.state.map (fun q => if elapsed < cutoff then Nat.pair elapsed q else sink n cutoff)⟩

theorem live_lt_sink (n cutoff elapsed q : Nat) (he : elapsed < cutoff) (hq : q < n) :
    Nat.pair elapsed q < sink n cutoff := by
  have ht : cutoff ≠ 0 := by omega
  rw [sink, if_neg ht]
  exact lt_trans (Nat.pair_lt_pair_left q he) (Nat.pair_lt_pair_right cutoff hq)

/-- Only a quadratic number of logical states is allocated in the cutoff
and original-state bounds. This is not a serialization-time statement. -/
theorem allocated_le (n cutoff : Nat) :
    allocated n cutoff ≤ (max n cutoff + 1)^2 + 1 := by
  by_cases ht : cutoff = 0
  · simp [allocated, sink, ht]
  · have h := Nat.pair_lt_max_add_one_sq cutoff n
    simp only [allocated, sink, ht, ↓reduceIte]
    rw [Nat.max_comm cutoff n] at h
    omega

/-- Every row targets an allocated state or accepts, even for malformed
original tables: out-of-range continuations are redirected to the sink. -/
theorem closed (n cutoff : Nat) (original : Nat → Bool → Row) :
    Closed (allocated n cutoff) (table n cutoff original) := by
  intro s _ read target htarget
  by_cases hs : s = sink n cutoff
  · simp [table, hs, sinkRow] at htarget
    subst target
    simp [allocated]
  · by_cases hp : (Nat.unpair s).1 < cutoff ∧ (Nat.unpair s).2 < n
    · cases hn : (original (Nat.unpair s).2 read).next with
      | none => simp [table, hs, hp, hn] at htarget
      | some q =>
        by_cases hnext : (Nat.unpair s).1 + 1 < cutoff ∧ q < n
        · simp [table, hs, hp, hn, hnext] at htarget
          subst target
          have hl := live_lt_sink n cutoff ((Nat.unpair s).1+1) q hnext.1 hnext.2
          simp only [allocated]
          omega
        · simp [table, hs, hp, hn, hnext, sinkRow] at htarget
          subst target
          simp [allocated]
    · simp [table, hs, hp, sinkRow] at htarget
      subst target
      simp [allocated]

/-- The sink remains nonaccepting on both symbols. It may continue to move
and alter the represented halves, so no tape-equality claim is made. -/
theorem sink_step (n cutoff : Nat) (original : Nat → Bool → Row) (c : Config)
    (h : c.state = some (sink n cutoff)) :
    (step (table n cutoff original) c).state = some (sink n cutoff) := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    simp [step, table, sinkRow]

theorem sink_run (n cutoff : Nat) (original : Nat → Bool → Row) (c : Config)
    (h : c.state = some (sink n cutoff)) (clock : Nat) :
    (run (table n cutoff original) c clock).state = some (sink n cutoff) := by
  induction clock with
  | zero => exact h
  | succ clock ih =>
    exact sink_step n cutoff original _ ih

theorem run_add (t : Nat → Bool → Row) (c : Config) (m k : Nat) :
    run t c (m+k) = run t (run t c m) k := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    change step t (run t c (m+k)) = step t (run t (run t c m) k)
    rw [ih]

theorem run_none (t : Nat → Bool → Row) (c : Config) (h : c.state = none) (k : Nat) :
    run t c k = c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [run, ih]
    cases c with
    | mk left right state =>
      simp only at h
      subst state
      rfl

/-- On each allocated live step, the guard performs exactly the original
write and move. An accepting row accepts even on the cutoff's final step. -/
theorem step_mapped (n cutoff elapsed : Nat) (original : Nat → Bool → Row)
    (c : Config) (he : elapsed < cutoff) (hc : Valid n c)
    (hclosed : Closed n original) :
    step (table n cutoff original) (mapped n cutoff elapsed c) =
      mapped n cutoff (elapsed+1) (step original c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      have hq : q < n := hc q rfl
      have hl := live_lt_sink n cutoff elapsed q he hq
      have hne : Nat.pair elapsed q ≠ sink n cutoff := ne_of_lt hl
      cases hr : (original q (right.testBit 0)).next with
      | none =>
        cases ht : (original q (right.testBit 0)).turn <;>
          simp only [Nat.testBit_zero] at hr ht <;>
          simp [mapped, he, step, table, hne, Nat.unpair_pair, hq, hr, ht]
      | some next =>
        have hnext : next < n := hclosed q hq (right.testBit 0) next hr
        by_cases htime : elapsed+1 < cutoff
        · cases ht : (original q (right.testBit 0)).turn <;>
            simp only [Nat.testBit_zero] at hr ht <;>
            simp [mapped, he, step, table, hne, Nat.unpair_pair, hq, hr, hnext, htime, ht]
        · cases ht : (original q (right.testBit 0)).turn <;>
            simp only [Nat.testBit_zero] at hr ht <;>
            simp [mapped, he, step, table, hne, Nat.unpair_pair, hq, hr, hnext, htime, ht]

/-- Before and at the cutoff, finite runs agree under the elapsed-state map.
The original run must stay in its finite state bound. -/
theorem run_mapped (n cutoff : Nat) (original : Nat → Bool → Row) (c : Config)
    (hc : Valid n c) (hclosed : Closed n original) (k : Nat) (hk : k ≤ cutoff) :
    run (table n cutoff original) (mapped n cutoff 0 c) k =
      mapped n cutoff k (run original c k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k ≤ cutoff := by omega
    have he : k < cutoff := by omega
    rw [run, ih hk', step_mapped n cutoff k original _ he
      (valid_run n original c hclosed hc k) hclosed]
    rfl

/-- The mapped original state zero is exactly the source-table start state
zero, including at cutoff zero where it is already the reject sink. -/
theorem mapped_start (n cutoff certificate input : Nat) :
    mapped n cutoff 0 ⟨certificate,input,some 0⟩ = ⟨certificate,input,some 0⟩ := by
  by_cases ht : cutoff = 0
  · simp [mapped, sink, ht]
  · have hp : 0 < cutoff := by omega
    simp [mapped, hp, Nat.pair]

/-- For every outer clock at least the original cutoff, acceptance agrees
with original acceptance exactly at that cutoff. This includes cutoff zero,
and does not assert equality of tapes after entering the reject sink. -/
theorem bounded_acceptance_stable (n cutoff : Nat) (original : Nat → Bool → Row)
    (c : Config) (hc : Valid n c) (hclosed : Closed n original) (extra : Nat) :
    (run (table n cutoff original) (mapped n cutoff 0 c) (cutoff+extra)).state.isNone =
      (run original c cutoff).state.isNone := by
  rw [run_add, run_mapped n cutoff original c hc hclosed cutoff (by omega)]
  cases h : (run original c cutoff).state with
  | none =>
    have hnone : (mapped n cutoff cutoff (run original c cutoff)).state = none := by
      simp [mapped, h]
    rw [run_none _ _ hnone]
    simp [mapped, h]
  | some q =>
    have hsink : (mapped n cutoff cutoff (run original c cutoff)).state =
        some (sink n cutoff) := by simp [mapped, h]
    rw [sink_run _ _ _ _ hsink]
    simp [h]

/-- The source-compatible start state is zero, even for zero cutoff. This
specialization retains arbitrary source input and certificate halves. -/
theorem initial_acceptance_stable (n cutoff : Nat) (original : Nat → Bool → Row)
    (hn : 0 < n) (hclosed : Closed n original) (certificate input extra : Nat) :
    (run (table n cutoff original) ⟨certificate,input,some 0⟩ (cutoff+extra)).state.isNone =
      (run original ⟨certificate,input,some 0⟩ cutoff).state.isNone := by
  have hv : Valid n ⟨certificate,input,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    omega
  have h := bounded_acceptance_stable n cutoff original
    ⟨certificate,input,some 0⟩ hv hclosed extra
  simpa only [mapped_start] using h

end Shared.Beeping.NPcoNP.Source284TableCountdown
