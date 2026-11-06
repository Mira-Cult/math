import Shared.Beeping.NPcoNP.Source284TableRun

/-! A finite source-relative table with a paid, certificate-preserving input
loader.  Loader correctness and cost are separate obligations; this module
defines its rows and proves that relocated original states simulate exactly.
No clock inflation, witness cutoff, or complexity claim is made. -/

namespace Shared.Beeping.NPcoNP.Source284HardwireTable

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun

/-- The loader contains one state per outgoing bit, one turning state, one
state per return bit, and one final turning state. -/
def offset (bits : List Bool) : Nat := 2 * bits.length + 2

def shiftRow (d : Nat) (r : Row) : Row :=
  ⟨r.write, r.turn, r.next.map (fun q => d + q)⟩

/-- Rows below `offset bits` write the supplied bits, turn, retrace them,
and turn back over the certificate. Rows above the offset are relocated
original rows. All loader rows are nonaccepting. -/
def table (bits : List Bool) (original : Nat → Bool → Row) (q : Nat) (read : Bool) : Row :=
  if q < bits.length then
    ⟨(bits[q]?).getD false, false, some (q + 1)⟩
  else if q = bits.length then
    ⟨false, true, some (q + 1)⟩
  else if q < 2 * bits.length + 1 then
    ⟨read, false, some (q + 1)⟩
  else if q = 2 * bits.length + 1 then
    ⟨read, true, some (q + 1)⟩
  else
    shiftRow (offset bits) (original (q - offset bits) read)

def shiftConfig (d : Nat) (c : Config) : Config :=
  ⟨c.left, c.right, c.state.map (fun q => d + q)⟩

theorem writing_row (bits : List Bool) (original : Nat → Bool → Row)
    (q : Nat) (hq : q < bits.length) (read : Bool) :
    table bits original q read = ⟨(bits[q]?).getD false, false, some (q+1)⟩ := by
  simp [table, hq]

theorem outward_turn_row (bits : List Bool) (original : Nat → Bool → Row)
    (read : Bool) :
    table bits original bits.length read = ⟨false, true, some (bits.length+1)⟩ := by
  simp [table]

theorem rewind_row (bits : List Bool) (original : Nat → Bool → Row)
    (j : Nat) (hj : j < bits.length) (read : Bool) :
    table bits original (bits.length + 1 + j) read =
      ⟨read, false, some (bits.length + 1 + j + 1)⟩ := by
  have h₁ : ¬ bits.length + 1 + j < bits.length := by omega
  have h₂ : bits.length + 1 + j ≠ bits.length := by omega
  have h₃ : bits.length + 1 + j < 2 * bits.length + 1 := by omega
  simp [table, h₁, h₂, h₃]

theorem return_turn_row (bits : List Bool) (original : Nat → Bool → Row)
    (read : Bool) :
    table bits original (2 * bits.length + 1) read =
      ⟨read, true, some (offset bits)⟩ := by
  have h₁ : ¬ 2 * bits.length + 1 < bits.length := by omega
  have h₂ : 2 * bits.length + 1 ≠ bits.length := by omega
  simp [table, offset, h₁, h₂]

theorem bit_read (right : Nat) : bit (right.testBit 0) = right % 2 := by
  rw [Nat.testBit_zero]
  have hm : right % 2 < 2 := Nat.mod_lt right (by decide)
  by_cases ho : right % 2 = 1
  · simp [bit, ho]
  · have hz : right % 2 = 0 := by omega
    simp [bit, ho, hz]

theorem bit_decide_mod (right : Nat) : bit (decide (right % 2 = 1)) = right % 2 := by
  simpa [Nat.testBit_zero] using bit_read right

theorem writing_step (bits : List Bool) (original : Nat → Bool → Row)
    (q left : Nat) (hq : q < bits.length) :
    step (table bits original) ⟨left, 0, some q⟩ =
      ⟨2 * left + bit ((bits[q]?).getD false), 0, some (q+1)⟩ := by
  simp [step, writing_row _ _ _ hq]

theorem outward_turn_step (bits : List Bool) (original : Nat → Bool → Row)
    (left : Nat) :
    step (table bits original) ⟨left, 0, some bits.length⟩ =
      ⟨0, left, some (bits.length+1)⟩ := by
  simp [step, outward_turn_row, bit]

theorem rewind_step (bits : List Bool) (original : Nat → Bool → Row)
    (j left right : Nat) (hj : j < bits.length) :
    step (table bits original) ⟨left, right, some (bits.length+1+j)⟩ =
      ⟨2 * left + right % 2, right / 2, some (bits.length+1+j+1)⟩ := by
  simp [step, rewind_row _ _ _ hj, bit_decide_mod]

/-- The final turn writes back the certificate's scanned bit and restores the
two halves, including when the certificate is zero. -/
theorem return_turn_step (bits : List Bool) (original : Nat → Bool → Row)
    (left certificate : Nat) :
    step (table bits original) ⟨left, certificate, some (2*bits.length+1)⟩ =
      ⟨certificate, left, some (offset bits)⟩ := by
  simp [step, return_turn_row, bit_decide_mod]
  omega

/-- Execute the first step before the remaining finite suffix. -/
theorem run_front (t : Nat → Bool → Row) (c : Config) (k : Nat) :
    run t c (k+1) = run t (step t c) k := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    change step t (run t c (k+1)) = step t (run t (step t c) k)
    rw [ih]

theorem relocated_row (bits : List Bool) (original : Nat → Bool → Row)
    (q : Nat) (read : Bool) :
    table bits original (offset bits + q) read =
      shiftRow (offset bits) (original q read) := by
  have h₁ : ¬ offset bits + q < bits.length := by simp [offset]; omega
  have h₂ : offset bits + q ≠ bits.length := by simp [offset]; omega
  have h₃ : ¬ offset bits + q < 2 * bits.length + 1 := by simp [offset]; omega
  have h₄ : offset bits + q ≠ 2 * bits.length + 1 := by simp [offset]; omega
  simp [table, h₁, h₂, h₃, h₄]

/-- Relocated source transitions preserve both tape halves, including the
write and move on the final accepting transition. -/
theorem relocated_step (bits : List Bool) (original : Nat → Bool → Row)
    (c : Config) :
    step (table bits original) (shiftConfig (offset bits) c) =
      shiftConfig (offset bits) (step original c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig, Option.map_some, step, relocated_row, shiftRow]
      split <;> rfl

theorem relocated_run (bits : List Bool) (original : Nat → Bool → Row)
    (c : Config) (clock : Nat) :
    run (table bits original) (shiftConfig (offset bits) c) clock =
      shiftConfig (offset bits) (run original c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih =>
    simp only [run, ih, relocated_step]

theorem relocated_acceptance (bits : List Bool) (original : Nat → Bool → Row)
    (c : Config) (clock : Nat) :
    (run (table bits original) (shiftConfig (offset bits) c) clock).state.isNone =
      (run original c clock).state.isNone := by
  rw [relocated_run]
  change ((run original c clock).state.map (fun q => offset bits + q)).isNone = _
  cases h : (run original c clock).state <;> simp [h]

/-- If the original rows are closed on `n` states, the complete table is
closed on the allocated bound `offset bits + n`. -/
theorem closed (bits : List Bool) (original : Nat → Bool → Row) (n : Nat)
    (hn : 0 < n) (horiginal : Closed n original) :
    Closed (offset bits + n) (table bits original) := by
  intro q hq read q' hnext
  unfold table at hnext
  split_ifs at hnext with hwrite hturn hback hlast
  · simp only [Option.some.injEq] at hnext
    subst q'
    simp only [offset]
    omega
  · simp only [Option.some.injEq] at hnext
    subst q'
    simp only [offset]
    omega
  · simp only [Option.some.injEq] at hnext
    subst q'
    simp only [offset]
    omega
  · simp only [Option.some.injEq] at hnext
    subst q'
    simp only [offset]
    omega
  · have hge : offset bits ≤ q := by simp only [offset]; omega
    have hq0 : q - offset bits < n := by omega
    cases hrow : (original (q - offset bits) read).next with
    | none => simp [shiftRow, hrow] at hnext
    | some target =>
      have htarget : target < n := horiginal _ hq0 read target hrow
      simp [shiftRow, hrow] at hnext
      subst q'
      omega

end Shared.Beeping.NPcoNP.Source284HardwireTable
