import Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
import Shared.Beeping.NPcoNP.NativeHalfLoopLayout
import Shared.Beeping.NPcoNP.NativeHalfSuffixShift

/-! Identify the exact cleanup tape with the unary bank and its reserve.
This is a tape equation; entry reachability and the logical HALF value
remain separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeHalfCleanupBank

open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.NativeHalfLoopLayout
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- A leading zero in an `after` suffix forms a fresh two-zero gap;
the appended reserve is part of the corresponding `before` suffix. -/
theorem after_zero_eq_before (base : Int → Bool) (gap : Int) (s : List Bool) :
    after base gap (false::s)=before base gap (s ++ [true,false]) := by
  funext p
  by_cases hp : p<gap
  · rw [after_prefix base gap p (false::s) hp,before_prefix base gap p (s ++ [true,false]) hp]
  by_cases hg : p=gap
  · subst p
    exact (gap_cells base gap (false::s)).2.2.trans (gap_cells base gap (s ++ [true,false])).1.symm
  by_cases hg1 : p=gap+1
  · subst p
    have ha := after_suffix_bit base gap (false::s) 0 (by simp)
    have hb := (gap_cells base gap (s ++ [true,false])).2.1
    simpa [bitAt] using ha.trans hb.symm
  have hpos : gap+2≤p := by omega
  let j := (p-gap-2).toNat
  have hjint : (j : Int)=p-gap-2 := by dsimp [j]; exact Int.toNat_of_nonneg (by omega)
  have hcoord : gap+2+(j : Int)=p := by omega
  have hb : before base gap (s ++ [true,false]) p=bitAt (s ++ [true,false]) j := by
    rw [← hcoord]
    exact before_suffix_bit base gap _ j
  rw [hb,bitAt_append_reserve]
  by_cases hj : j<s.length
  · have hmem : j+1<(false::s).length := by simp; omega
    have ha := after_suffix_bit base gap (false::s) (j+1) hmem
    have hc : gap+1+(((j+1 : Nat)) : Int)=p := by push_cast; omega
    rw [hc] at ha
    have hbit : bitAt (false::s) (j+1)=bitAt s j := by simp [bitAt]
    rw [hbit] at ha
    simpa only [hj,if_true] using ha
  · by_cases he : j=s.length
    · have hc : gap+1+((false::s).length : Int)=p := by simp only [List.length_cons,Nat.cast_succ]; omega
      have ha := (appended_zero_block base gap (false::s)).1
      rw [hc] at ha
      simpa only [he,Nat.lt_irrefl,if_false,if_true] using ha
    · have ht : gap+1+((false::s).length : Int)<p := by
        simp only [List.length_cons,Nat.cast_succ]
        omega
      have ha := after_tail_zero base gap p (false::s) ht
      simpa only [hj,he,if_false] using ha

/-- The cleanup preserves the encoded active suffix and appends two zero
blocks in total, one in the suffix and one in the `after` reserve. -/
theorem postTape_as_bank (base : Int → Bool) (b : Int) (values : List Nat) :
    postTape base b values = after base (b+1) (encode (values ++ [0])) := by
  unfold postTape
  dsimp only
  rw [after_zero_eq_before]
  rw [append_zero_block]
  have h := spec_before_eq_after base (b+1) (encode values ++ [true,false])
  have hl : (encode values ++ [true,false]).length=(encode values).length+2 := by simp
  rw [hl] at h
  have hp : (b+1)+1+(((encode values).length+2 : Nat) : Int) =
      b+3+(((false :: encode values).length : Nat) : Int) := by
    simp only [List.length_cons,Nat.cast_succ]
    omega
  rw [hp] at h
  exact h

end Shared.Beeping.NPcoNP.NativeHalfCleanupBank

#print axioms Shared.Beeping.NPcoNP.NativeHalfCleanupBank.postTape_as_bank
