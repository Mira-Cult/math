import Shared.Beeping.NPcoNP.NativeAllZeroToUnitWords
import Shared.Beeping.NPcoNP.NativeUnitTerminalLayoutExact

/-! Tape facts needed to continue an all-zero fill through the existing
unit/terminal macro. They are conditional on the supplied marker and
delimiter; they do not establish a recurring blank-start invariant. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroTerminalReady
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncBlock
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroToUnit
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- No cell at or to the right of the fill's end is changed. -/
theorem filled_after (a : Int) (r : Nat) (t : Int → Bool) (q : Int)
    (h : a+34+(r : Int)≤q) : filled a r t q=t q := by
  change (if a+32≤q ∧ q<a+34+(r : Int) then true else
    if q=a+30 then true else t q)=t q
  rw [if_neg (by omega),if_neg (by omega)]

/-- The fill, the supplied right marker, and the following zero form the
finite one-run needed by the next physical increment. -/
theorem filled_scanword (a : Int) (r : Nat) (t : Int → Bool)
    (marker : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false) :
    Holds (filled a r t) (a+32) (List.replicate (r+3) true ++ [false]) := by
  apply holds_ones_delimiter (r+3) (a+32) (filled a r t)
  · intro i hi
    by_cases hs : i<r+2
    · change (if a+32≤a+32+(i : Int) ∧ a+32+(i : Int)<a+34+(r : Int)
        then true else setAt (a+30) t (a+32+(i : Int)))=true
      rw [if_pos (by omega)]
    · have he : i=r+2 := by omega
      subst i
      have hp : a+32+((r+2 : Nat) : Int)=a+34+(r : Int) := by push_cast; omega
      rw [hp,filled_after a r t _ (by omega)]
      exact marker
  · have hp : a+32+((r+3 : Nat) : Int)=a+35+(r : Int) := by push_cast; omega
    rw [hp,filled_after a r t _ (by omega)]
    exact delimiter

theorem terminal_word :
    markerWindow (List.replicate 13 0 ++ [1]) =
      markerWindow (List.replicate 13 0 ++ [0]) ++ [true] := by decide

/-- The longer terminal selector word is already present: the old marker
is its last bit, and the fill is strictly to its right. -/
theorem filled_terminal_window (a : Int) (r : Nat) (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (marker : t (a+28)=true) :
    Holds (filled a r t) a (markerWindow (List.replicate 13 0 ++ [1])) := by
  let old := markerWindow (List.replicate 13 0 ++ [0])
  have hl : old.length=28 := by decide
  have ht : Holds t (a+((old.length : Nat) : Int)) [true] := by
    rw [hl]
    simpa [Holds] using marker
  have hword : Holds t a (old++[true]) := holds_append_intro t a old [true] window ht
  have hlen : (old++[true]).length=29 := by simp [hl]
  have hfilled : Holds (filled a r t) a (old++[true]) := by
    apply holds_transport t _ a _ hword
    intro q _ hq
    rw [hlen] at hq
    exact (filled_before a r t q (by omega)).symm
  rw [terminal_word]
  exact hfilled

/-- Any following bank word is retained in full, not merely its first
few decoded values. -/
theorem filled_bank (a : Int) (r : Nat) (t : Int → Bool) (xs : List Bool)
    (bank : Holds t (a+36+(r : Int)) xs) :
    Holds (filled a r t) (a+36+(r : Int)) xs := by
  apply holds_transport t _ _ xs bank
  intro q hq _
  exact (filled_after a r t q (by omega)).symm

/-- The earlier marker is not created by the fill and must be supplied
separately for the terminal selector. -/
theorem filled_earlier_marker (a : Int) (r : Nat) (t : Int → Bool)
    (marker : t (a-1)=true) : filled a r t (a-1)=true := by
  rw [filled_before a r t (a-1) (by omega)]
  exact marker

#print axioms filled_scanword
#print axioms filled_terminal_window
#print axioms filled_bank
end Shared.Beeping.NPcoNP.NativeAllZeroTerminalReady
