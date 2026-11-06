import Shared.Beeping.NPcoNP.NativeHalfSweepShape
import Shared.Beeping.NPcoNP.NativeHalfCleanupScan

/-! Descending tape shape for the reverse cleanup immediately following the
exceptional zero-prefixed suffix scan. This is a tape fact for supplied
configurations; it does not establish reachability or execute the cleanup. -/
namespace Shared.Beeping.NPcoNP.NativeHalfCleanupShape
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The finite reverse bank is admissible after the leading zero/one pair. -/
theorem cleanup_shape (values : List Nat) :
    ∃ s : Shape, bits s = false :: true :: (UnaryBank.encode values).reverse := by
  obtain ⟨s, hs⟩ := shape_reverse_bank values
  exact ⟨.zeroOne s, by simp [bits, hs]⟩

/-- From the state-20 endpoint of the forward scan, the reverse cleanup sees
`01`, the bank in reverse order, and the two zero delimiters. -/
theorem down_after_zero_bank (base : Int → Bool) (gap : Int) (values : List Nat) :
    let bank := UnaryBank.encode values
    let suffix := false :: bank
    downHolds (after base gap suffix) (gap + 2 + (suffix.length : Int))
      ((false :: true :: bank.reverse) ++ [false,false]) := by
  dsimp only
  apply down_of_get
  intro i hi
  let bank := UnaryBank.encode values
  let suffix := false :: bank
  change (after base gap suffix) (gap + 2 + (suffix.length : Int) - (i : Int)) =
    (((false :: true :: bank.reverse) ++ [false,false])[i])
  have hb : i < bank.length + 4 := by
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse] at hi
    dsimp [bank]
    omega
  by_cases h0 : i = 0
  · subst i
    simpa [suffix] using (appended_zero_block base gap (false :: bank)).2
  by_cases h1 : i = 1
  · subst i
    change after base gap suffix (gap + 2 + (suffix.length : Int) - 1) = true
    have he : gap + 2 + (suffix.length : Int) - 1 =
        gap + 1 + ((false :: bank).length : Int) := by dsimp [suffix]; omega
    rw [he]
    exact (appended_zero_block base gap (false :: bank)).1
  by_cases hr : i < bank.length + 2
  · have hilo : 2 ≤ i := by omega
    let j := i - 2
    have hj : j < bank.length := by dsimp [j]; omega
    have hlen : i < (false :: true :: bank.reverse).length := by simp; omega
    rw [List.getElem_append_left hlen]
    have hg : (false :: true :: bank.reverse)[i] = bank.reverse[j]'(by simpa using hj) := by
      -- Rewrite the index as two successors.
      have he : i = j + 2 := by dsimp [j]; omega
      simpa only [he, List.getElem_cons_succ]
    rw [hg, List.getElem_reverse]
    have hk : bank.length - 1 - j < bank.length := by omega
    have he : gap + 2 + ((suffix.length : Nat) : Int) - (i : Int) =
        gap + 1 + (((bank.length - 1 - j) + 1 : Nat) : Int) := by
      dsimp [suffix, j]; (try simp only [List.length_cons, Nat.cast_add, Nat.cast_one]); omega
    rw [he, after_suffix_bit base gap suffix _ (by dsimp [suffix]; simp; omega)]
    simp [bitAt, suffix, List.getElem?_eq_getElem hk]
  · have he : i = bank.length + 2 ∨ i = bank.length + 3 := by omega
    rcases he with h2 | h3
    · subst i
      have hp : gap + 2 + ((suffix.length : Nat) : Int) - ((bank.length + 2 : Nat) : Int) = gap + 1 := by
        dsimp [suffix]; (try simp only [List.length_cons, Nat.cast_add, Nat.cast_one]); omega
      rw [hp]
      have hx := after_suffix_bit base gap suffix 0 (by dsimp [suffix]; simp)
      simp only [Nat.cast_zero, add_zero] at hx
      rw [hx]
      simp [suffix, bitAt, List.getElem_append_right]
    · subst i
      have hp : gap + 2 + ((suffix.length : Nat) : Int) - ((bank.length + 3 : Nat) : Int) = gap := by
        dsimp [suffix]; (try simp only [List.length_cons, Nat.cast_add, Nat.cast_one]); omega
      rw [hp]
      simp [gap_cells, suffix, List.getElem_append_right]

end Shared.Beeping.NPcoNP.NativeHalfCleanupShape
