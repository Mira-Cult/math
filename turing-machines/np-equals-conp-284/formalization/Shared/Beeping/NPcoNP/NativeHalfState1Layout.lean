import Shared.Beeping.NPcoNP.NativeHalfReturnBank

/-! Tape layout before the literal state-1 carry scan, when the protected
prefix is the prepared encoded bank used by `NativeHalfReturnBank`. The
leftward run of ones still needs a separate finite-delimiter hypothesis for
the actual machine scan. These are layout facts, not reachability. -/

namespace Shared.Beeping.NPcoNP.NativeHalfState1Layout

open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.UnarySuffixShift

def leftSuffix (left : List Nat) : List Bool := UnaryBank.encode left ++ [true]

def preparedTape (back : Int → Bool) (gap : Int) (left values : List Nat) : Int → Bool :=
  let suffix := leftSuffix left
  let base := before back gap suffix
  let b := gap + 1 + (suffix.length : Int)
  postTape base b values

theorem suffix_length_pos (left : List Nat) : 0 < (leftSuffix left).length := by
  simp [leftSuffix]

theorem suffix_first (left : List Nat) : bitAt (leftSuffix left) 0 = true := by
  cases left with
  | nil => simp [leftSuffix, UnaryBank.encode, bitAt]
  | cons n ns => simp [leftSuffix, UnaryBank.encode, UnaryBank.block, List.replicate_succ, bitAt]

/-- The cleanup preserves the two-zero gap and the first suffix one. -/
theorem prepared_gap (back : Int → Bool) (gap : Int) (left values : List Nat) :
    preparedTape back gap left values gap = false ∧
      preparedTape back gap left values (gap + 1) = false ∧
      preparedTape back gap left values (gap + 2) = true := by
  let suffix := leftSuffix left
  let base := before back gap suffix
  let b := gap + 1 + (suffix.length : Int)
  have hp : 0 < (suffix.length : Int) := by exact_mod_cast suffix_length_pos left
  have h0 : gap ≤ b := by dsimp [b]; omega
  have h1 : gap + 1 ≤ b := by dsimp [b]; omega
  have h2 : gap + 2 ≤ b := by dsimp [b]; omega
  change postTape base b values gap = false ∧
    postTape base b values (gap + 1) = false ∧
    postTape base b values (gap + 2) = true
  rw [postTape_prefix base b gap values h0,
    postTape_prefix base b (gap + 1) values h1,
    postTape_prefix base b (gap + 2) values h2]
  have hs : before back gap suffix (gap + 2) = true := by
    rw [show gap + 2 = gap + 2 + (0 : Nat) by simp, before_suffix_bit]
    exact suffix_first left
  exact ⟨(gap_cells back gap suffix).1, (gap_cells back gap suffix).2.1, hs⟩

/-- Cleanup and its suffix construction preserve the arbitrary tape strictly
left of the old gap. -/
theorem prepared_prefix (back : Int → Bool) (gap p : Int) (left values : List Nat)
    (hp : p < gap) : preparedTape back gap left values p = back p := by
  let suffix := leftSuffix left
  let base := before back gap suffix
  let b := gap + 1 + (suffix.length : Int)
  have hb : p ≤ b := by dsimp [b]; omega
  change postTape base b values p = back p
  rw [postTape_prefix base b p values hb]
  exact before_prefix back gap p suffix hp

/-- Any finite downward pattern in the protected tape to the left of the
gap remains available to the state-1 carry scan. -/
theorem prepared_downHolds (back : Int → Bool) (gap h : Int) (left values : List Nat)
    (xs : List Bool) (hh : h < gap) (hm : downHolds back h xs) :
    downHolds (preparedTape back gap left values) h xs := by
  induction xs generalizing h with
  | nil => trivial
  | cons x xs ih =>
    simp only [downHolds] at hm ⊢
    constructor
    · rw [prepared_prefix back gap h left values hh]
      exact hm.1
    · exact ih (h - 1) (by omega) hm.2

end Shared.Beeping.NPcoNP.NativeHalfState1Layout
