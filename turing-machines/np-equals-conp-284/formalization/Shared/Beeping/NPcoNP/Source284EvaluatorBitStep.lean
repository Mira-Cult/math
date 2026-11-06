import Shared.Beeping.NPcoNP.Source284RecordTM2
import Shared.Beeping.NPcoNP.Source284UnaryCountBits
import Shared.Codes.BinaryAdditionCanonical

/-! An executable raw-bit representation of one bounded source-evaluator
step.  All code, tape halves, and state are finite Boolean lists, including
noncanonical high zeroes. This file proves extensional step correctness; it
does not yet prove canonical polynomial time for this whole step or loop. -/

namespace Shared.Beeping.NPcoNP.Source284EvaluatorBitStep

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284RecordBitCost
open Shared.Beeping.NPcoNP.Source284UnaryCountBits

structure Config where
  left : List Bool
  right : List Bool
  state : List Bool
  deriving DecidableEq, Repr

def denote (c : Config) : Source284Relative.Config :=
  ⟨value c.left,value c.right,value c.state⟩

def bitValue (b : Bool) : Nat := if b then 1 else 0

/-- A binary state is decremented only in the active branch. If the scanned
bit is one, the ordinal is then incremented, matching `state - 1 + read`. -/
def ordinal (s : List Bool) (read : Bool) : List Bool :=
  if read then incrementData (decBits s) else decBits s

def step (code : List Bool) (c : Config) : Config :=
  if isZero c.state then c else
    let row := (Source284RecordTM2.lookup (code,ordinal c.state (c.right.headD false))).bits
    let written := row.headD false
    let turn := row.tail.headD false
    let next := row.tail.tail
    let forward := c.right.tail
    if turn then ⟨written :: forward,c.left,next⟩
    else ⟨written :: c.left,forward,next⟩

theorem value_head (xs : List Bool) : bitValue (xs.headD false) = value xs % 2 := by
  cases xs with
  | nil => rfl
  | cons b bs => cases b <;> simp [bitValue, value] <;> omega

theorem value_tail (xs : List Bool) : value xs.tail = value xs / 2 := by
  cases xs with
  | nil => rfl
  | cons b bs => cases b <;> simp [value] <;> omega

theorem increment_value (xs : List Bool) : value (incrementData xs) = value xs + 1 := by
  rw [incrementData_eq]
  exact Shared.Codes.BitTableValidation.increment_value xs

theorem ordinal_value (s : List Bool) (read : Bool) (h : value s ≠ 0) :
    value (ordinal s read) = value s - 1 + bitValue read := by
  have hd := decBits_correct s (by omega)
  cases read <;> simp [ordinal, bitValue, increment_value] <;> omega

/-- One data-only bit step denotes exactly the source's bounded evaluator
step; accepting state zero remains absorbing. -/
theorem step_correct (code : List Bool) (c : Config) :
    denote (step code c) = Source284Relative.step (value code) (denote c) := by
  rcases c with ⟨left,right,state⟩
  by_cases hz : isZero state = true
  · have hstate : value state = 0 := (isZero_correct state).1 hz
    simp [step, hz, denote, Source284Relative.step, hstate]
  · have hstate : value state ≠ 0 := by
      intro h
      exact hz ((isZero_correct state).2 h)
    have hr := value_head right
    have hi := ordinal_value state (right.headD false) hstate
    rw [hr] at hi
    have hrow : Source284Relative.record (value code) (value state - 1 + value right % 2) =
        Source284RecordTM2.lookup (code,ordinal state (right.headD false)) := by
      rw [← hi]
      exact (Source284RecordTM2.lookup_correct code _).symm
    let row := Source284RecordTM2.lookup (code,ordinal state (right.headD false))
    have hv : value row.bits = row := Shared.Codes.BinaryAdditionCanonical.value_bits row
    have hw : bitValue (row.bits.headD false) = row % 2 := by
      rw [value_head, hv]
    have ht : bitValue (row.bits.tail.headD false) = (row / 2) % 2 := by
      rw [value_head, value_tail, hv]
    have hn : value row.bits.tail.tail = row / 4 := by
      rw [value_tail, value_tail, hv]
      omega
    have hf := value_tail right
    change Source284Relative.record (value code) (value state - 1 + value right % 2) = row at hrow
    simp only [step, hz, Bool.false_eq_true, ↓reduceIte, denote,
      Source284Relative.step, hstate]
    simp only [hrow]
    change denote (if row.bits.tail.headD false then
        ⟨row.bits.headD false :: right.tail,left,row.bits.tail.tail⟩ else
        ⟨row.bits.headD false :: left,right.tail,row.bits.tail.tail⟩) =
      (if (row / 2) % 2 = 1 then ⟨2 * (value right / 2) + row % 2,value left,row / 4⟩ else
        ⟨2 * value left + row % 2,value right / 2,row / 4⟩)
    have hturn : (row / 2) % 2 = 1 ↔ row.bits.tail.headD false = true := by
      rw [← ht]
      cases h : row.bits.tail.headD false <;> simp [bitValue, h]
    by_cases hb : row.bits.tail.headD false = true
    · have hp : (row / 2) % 2 = 1 := hturn.mpr hb
      simp only [hb, hp, ↓reduceIte, denote]
      change Source284Relative.Config.mk (2 * value right.tail + bitValue (row.bits.headD false))
          (value left) (value row.bits.tail.tail) = _
      rw [hf, hw, hn]
    · have hp : (row / 2) % 2 ≠ 1 := fun h => hb (hturn.mp h)
      simp only [hb, hp, ↓reduceIte, denote]
      change Source284Relative.Config.mk (2 * value left + bitValue (row.bits.headD false))
          (value right.tail) (value row.bits.tail.tail) = _
      rw [hf, hw, hn]

end Shared.Beeping.NPcoNP.Source284EvaluatorBitStep
