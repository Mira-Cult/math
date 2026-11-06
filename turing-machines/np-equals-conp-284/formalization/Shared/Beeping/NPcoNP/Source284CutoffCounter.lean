import Shared.Beeping.NPcoNP.Source284TableRun

/-! A finite source-relative unary token counter segment.  The head faces
`n` consecutive one bits followed by a zero delimiter. Each counted token is
erased and crossed in one transition. Crossing the zero selects a continuing
handoff state; it does not halt or accept. The unread high tail is preserved.

This is a logical source table, not a count of physical beeper states. It does
not construct the unary counter, synchronize it with the witness scanner, or
provide a dynamic witness cutoff guard. In particular, its unary space is `n`
cells and producing those cells and moving between counter and witness must be
charged separately. -/

namespace Shared.Beeping.NPcoNP.Source284CutoffCounter

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun

/-- State zero consumes one token or crosses the delimiter. State one is a
continuing handoff that moves without changing the scanned bit. -/
def table : Nat → Bool → Row
  | 0, true => ⟨false, false, some 0⟩
  | 0, false => ⟨false, false, some 1⟩
  | _, b => ⟨b, false, some 1⟩

theorem table_closed : Closed 2 table := by
  intro q hq b q' hnext
  interval_cases q <;> cases b <;> simp_all [table] <;> omega

/-- Low-first unary tokens, a zero delimiter, then an arbitrary high tail. -/
def tokens : Nat → Nat → Nat
  | 0, tail => 2 * tail
  | n+1, tail => 2 * tokens n tail + 1

/-- One transition erases one token and advances the tape head. -/
theorem consume (left tail n : Nat) :
    step table ⟨left, tokens (n+1) tail, some 0⟩ =
      ⟨2*left, tokens n tail, some 0⟩ := by
  simp [step, table, tokens, Nat.testBit_zero, bit] <;> omega

/-- One transition crosses the zero delimiter into the handoff state. -/
theorem finish (left tail : Nat) :
    step table ⟨left, tokens 0 tail, some 0⟩ =
      ⟨2*left, tail, some 1⟩ := by
  simp [step, table, tokens, Nat.testBit_zero, bit]

theorem run_add (c : Config) (a b : Nat) :
    run table c (a+b) = run table (run table c a) b := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    change step table (run table c (a+b)) = step table (run table (run table c a) b)
    rw [ih]

/-- Exactly `n` paid source steps erase and cross all tokens. -/
theorem consume_all (n left tail : Nat) :
    run table ⟨left, tokens n tail, some 0⟩ n =
      ⟨2^n * left, tokens 0 tail, some 0⟩ := by
  induction n generalizing left with
  | zero => simp [run]
  | succ n ih =>
    have h := run_add ⟨left, tokens (n+1) tail, some 0⟩ 1 n
    change run table ⟨left, tokens (n+1) tail, some 0⟩ (1+n) =
      run table (step table ⟨left, tokens (n+1) tail, some 0⟩) n at h
    rw [consume, ih] at h
    simpa [Nat.add_comm, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- `n+1` paid steps select the handoff, with no dependence on the tail. -/
theorem complete (n left tail : Nat) :
    run table ⟨left, tokens n tail, some 0⟩ (n+1) =
      ⟨2^(n+1) * left, tail, some 1⟩ := by
  rw [run_add, consume_all]
  simp only [run, finish]
  congr 1
  simp only [pow_succ]
  ring

/-- The two logical states use four records in the source table. -/
theorem record_count : (records 2 table).length = 4 := by
  simp [records]

def description : Nat := encode 2 table 0

/-- The actual numeric source table performs the same finite counter pass.
The left half is arbitrary, and the right half contains the unary counter. -/
theorem source_complete (n left tail : Nat) :
    Source284Relative.run description
      (Source284Relative.initial (tokens n tail) left) (n+1) =
      ⟨2^(n+1) * left, tail, active 1⟩ := by
  have hv : Valid 2 ⟨left, tokens n tail, some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    omega
  have hs := run_toSource 2 table 0 ⟨left, tokens n tail, some 0⟩ table_closed hv (n+1)
  change Source284Relative.run description
    (Source284Relative.initial (tokens n tail) left) (n+1) = _ at hs
  rw [hs, complete]
  rfl

end Shared.Beeping.NPcoNP.Source284CutoffCounter
