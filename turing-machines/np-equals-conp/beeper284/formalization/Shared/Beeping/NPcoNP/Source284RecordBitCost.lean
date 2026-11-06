import Shared.Beeping.NPcoNP.Source284RecordBits

namespace Shared.Beeping.NPcoNP.Source284RecordBitCost

def isZero : List Bool → Bool
  | [] => true
  | false :: xs => isZero xs
  | true :: _ => false

def decBits : List Bool → List Bool
  | [] => []
  | true :: xs => false :: xs
  | false :: xs => true :: decBits xs

@[simp] theorem decBits_length (xs : List Bool) : (decBits xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [decBits, ih]

/-- Unary result: one list cell per one before the delimiter of the indexed record. -/
def scan : List Bool → List Bool → List Bool
  | [], _ => []
  | bit :: bits, index =>
      if isZero index then
        if bit then true :: scan bits index else []
      else scan bits (if bit then index else decBits index)

/-- The unary result allocates at most one cell per supplied source bit. -/
theorem scan_length_le (code idx : List Bool) : (scan code idx).length ≤ code.length := by
  induction code generalizing idx with
  | nil => simp [scan]
  | cons b bs ih =>
    have hi := ih idx
    have hd := ih (decBits idx)
    cases b <;> by_cases hz : isZero idx = true <;>
      simp [scan, hz] at * <;> omega

/-- The following recurrence declares a cost model that conservatively
charges one unit per examined bit, cons cell, or branch. Proof-only natural
numbers used to state costs are not runtime data. This is not a proof of the
running time of a concrete tape machine, nor is it tied to a separately
formalized small-step cost semantics. Empty source input returns immediately
for every index. -/
def isZeroCost : List Bool → Nat
  | [] => 1
  | false :: xs => 2 + isZeroCost xs
  | true :: _ => 2

def decCost : List Bool → Nat
  | [] => 1
  | true :: _ => 3
  | false :: xs => 3 + decCost xs

def scanCost : List Bool → List Bool → Nat
  | [], _ => 1
  | bit :: bits, index =>
      6 + isZeroCost index +
        if isZero index then
          if bit then 1 + scanCost bits index else 0
        else if bit then scanCost bits index else decCost index + scanCost bits (decBits index)

theorem isZeroCost_le (idx : List Bool) : isZeroCost idx ≤ 2 * idx.length + 1 := by
  induction idx with
  | nil => simp [isZeroCost]
  | cons b bs ih => cases b <;> simp [isZeroCost, ih] <;> omega

theorem decCost_le (idx : List Bool) : decCost idx ≤ 3 * idx.length + 1 := by
  induction idx with
  | nil => simp [decCost]
  | cons b bs ih => cases b <;> simp [decCost, ih] <;> omega

theorem scanCost_le (code idx : List Bool) :
    scanCost code idx ≤ (code.length + 1) * (5 * idx.length + 10) := by
  induction code generalizing idx with
  | nil => simp [scanCost]
  | cons b bs ih =>
    have hz := isZeroCost_le idx
    have hd := decCost_le idx
    have hi := ih idx
    have hid := ih (decBits idx)
    simp only [decBits_length] at hid
    cases b <;> by_cases h : isZero idx = true <;>
      simp [scanCost, h, List.length_cons] at * <;> nlinarith


open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284RecordBits

theorem isZero_correct (idx : List Bool) : isZero idx = true ↔ value idx = 0 := by
  induction idx with
  | nil => simp [isZero, value]
  | cons b bs ih =>
    cases b <;> simp [isZero, value, ih] <;> omega

theorem decBits_correct (idx : List Bool) (hp : 0 < value idx) :
    value (decBits idx) + 1 = value idx := by
  induction idx with
  | nil => simp [value] at hp
  | cons b bs ih =>
    cases b with
    | false =>
      have h : 0 < value bs := by simp [value] at hp; omega
      have hd := ih h
      simp [decBits, value] at *
      omega
    | true => simp [decBits, value]

@[simp] theorem recordBits_nil (ordinal : Nat) : recordBits [] ordinal = 0 := by
  induction ordinal with
  | zero => rfl
  | succ k ih => simpa [recordBits, dropBits, readBits] using ih

@[simp] theorem recordBits_false_zero (bs : List Bool) : recordBits (false :: bs) 0 = 0 := by
  simp [recordBits, dropBits, readBits]

@[simp] theorem recordBits_true_zero (bs : List Bool) :
    recordBits (true :: bs) 0 = recordBits bs 0 + 1 := by
  simp [recordBits, dropBits, readBits]

@[simp] theorem recordBits_false_succ (bs : List Bool) (n : Nat) :
    recordBits (false :: bs) (n+1) = recordBits bs n := by
  simp [recordBits, dropBits, readBits]

@[simp] theorem recordBits_true_succ (bs : List Bool) (n : Nat) :
    recordBits (true :: bs) (n+1) = recordBits bs (n+1) := by
  simp [recordBits, dropBits, readBits]

/-- The actual list scanner agrees with virtual-zero record lookup for every
binary index, including redundant high zero bits and arbitrarily large indices. -/
theorem scan_correct (code idx : List Bool) :
    (scan code idx).length = recordBits code (value idx) := by
  induction code generalizing idx with
  | nil => simp [scan]
  | cons b bs ih =>
    by_cases hz : isZero idx = true
    · have hn : value idx = 0 := (isZero_correct idx).1 hz
      cases b <;> simp [scan, hz, hn, ih, Nat.add_comm]
    · have hn : value idx ≠ 0 := by
        intro h
        exact hz ((isZero_correct idx).2 h)
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hd := decBits_correct idx (by omega)
      have hd' : value (decBits idx) = n := by omega
      cases b <;> simp [scan, hz, ih, hn, hd']

end Shared.Beeping.NPcoNP.Source284RecordBitCost
