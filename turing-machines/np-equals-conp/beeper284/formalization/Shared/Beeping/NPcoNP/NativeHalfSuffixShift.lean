import Shared.Beeping.NPcoNP.NativeHalfSweepSpec
import Shared.Beeping.NPcoNP.NativeHalfSweepShape
import Shared.Beeping.NPcoNP.NativeHalfTapeScan

/-! The literal 284-state machine realizes one complete unary suffix shift.
The prepared tape contains a two-zero gap, a nonempty finite encoded suffix,
and an all-zero right tail. The result has the suffix shifted left by one,
one additional `10` zero-reserve block, and an unchanged protected prefix.
This local theorem does not establish reachability of the prepared tape,
the complete HALF operation, or the source-to-machine refinement. -/
namespace Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.UnarySuffixShift

theorem spec_before_eq_after (base : Int → Bool) (gap : Int) (suffix : List Bool) :
    spec (before base gap suffix) (gap+1+suffix.length) suffix.length =
      after base gap suffix := by
  funext i
  let h : Int := gap+1+suffix.length
  have hk : (0 : Int) ≤ suffix.length := by omega
  by_cases hleft : i < gap
  · have ho : i < h - (suffix.length : Int) := by dsimp [h]; omega
    rw [spec_outside _ _ _ _ (Or.inl ho), before_prefix _ _ _ _ hleft,
      after_prefix _ _ _ _ hleft]
  · by_cases hg : i = gap
    · subst i
      have ho : gap < h - (suffix.length : Int) := by dsimp [h]; omega
      rw [spec_outside _ _ _ _ (Or.inl ho)]
      exact (gap_cells base gap suffix).1.trans (gap_cells base gap suffix).2.2.symm
    · by_cases htop : i = h
      · subst i
        rw [spec_top]
        dsimp [h]
        exact (appended_zero_block base gap suffix).1.symm
      · by_cases hin : i < h
        · have hlo : h - (suffix.length : Int) ≤ i := by dsimp [h]; omega
          rw [spec_inside _ _ _ _ hlo hin]
          let j : Nat := (i - gap - 1).toNat
          have hjint : (j : Int) = i-gap-1 := by dsimp [j]; rw [Int.toNat_of_nonneg]; omega
          have hj : j < suffix.length := by dsimp [h] at hin; omega
          calc
            before base gap suffix (i+1) = before base gap suffix (gap+2+(j:Int)) := by congr 1 <;> omega
            _ = bitAt suffix j := before_suffix_bit base gap suffix j
            _ = after base gap suffix (gap+1+(j:Int)) := (after_suffix_bit base gap suffix j hj).symm
            _ = after base gap suffix i := by congr 1 <;> omega
        · have hr : h < i := by omega
          rw [spec_outside _ _ _ _ (Or.inr hr)]
          have hb : before base gap suffix i = false := before_tail_zero base gap i suffix (by dsimp [h] at hr; omega)
          have ha : after base gap suffix i = false := after_tail_zero base gap i suffix (by dsimp [h] at hr; omega)
          rw [hb, ha]
end Shared.Beeping.NPcoNP.NativeHalfSweep
namespace Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Table284

theorem selected_before_sweep (base : Int → Bool) (gap : Int) (values : List Nat) :
    silentSegment machine
      (cfg 34 (gap+1+(UnaryBank.encode values).length) (before base gap (UnaryBank.encode values)))
      (cfg 31 (gap-1) (after base gap (UnaryBank.encode values)))
      ((UnaryBank.encode values).length + 2) := by
  let suffix := UnaryBank.encode values
  obtain ⟨s, hs⟩ := shape_reverse_bank values
  have hd := down_before_reverse base gap suffix
  have hd' : downHolds (before base gap suffix) (gap+1+suffix.length) (bits s ++ [false,false]) := by
    simpa [suffix, hs] using hd
  have hl : (bits s).length = suffix.length := by simpa [suffix, hs]
  have h := sweep_spec s (gap+1+suffix.length) (before base gap suffix) hd'
  rw [hl, spec_before_eq_after] at h
  have hp : gap+1+(suffix.length : Int)-(suffix.length : Int)-2 = gap-1 := by omega
  rw [hp] at h
  simpa only [suffix] using h

theorem prefix_length (x : Nat) (xs : List Nat) :
    (unaryBankPrefix x xs).length + 1 = (UnaryBank.encode (x::xs)).length := by
  have h := congrArg List.length (bank_prefix_identity x xs)
  simp only [List.length_append, List.length_cons, List.length_nil] at h
  omega

theorem selected_suffix_shift (base : Int → Bool) (gap : Int) (x : Nat) (xs : List Nat) :
    let suffix := UnaryBank.encode (x::xs)
    silentSegment machine
      (cfg 32 (gap+2) (before base gap suffix))
      (cfg 31 (gap-1) (after base gap suffix))
      (2*suffix.length + 3) := by
  dsimp only
  let suffix := UnaryBank.encode (x::xs)
  have hl := prefix_length x xs
  have hscan := selected_before_bank base gap x xs
  have hscan' : silentSegment machine
      (cfg 32 (gap+2) (before base gap suffix))
      (cfg 34 (gap+1+suffix.length) (before base gap suffix)) (suffix.length+1) := by
    have he : gap+2+((unaryBankPrefix x xs).length : Int) = gap+1+(suffix.length : Int) := by
      dsimp [suffix]; omega
    have hn : (unaryBankPrefix x xs).length + 2 = suffix.length + 1 := by dsimp [suffix]; omega
    rw [he, hn] at hscan
    exact hscan
  have hsweep := selected_before_sweep base gap (x::xs)
  have hseg := segAdd machine _ _ _ (suffix.length+1) (suffix.length+2) hscan' hsweep
  dsimp only [suffix] at hseg
  convert hseg using 1 <;> omega

theorem selected_suffix_shift_positive (x : Nat) (xs : List Nat) :
    0 < 2 * (UnaryBank.encode (x::xs)).length + 3 := by omega

theorem selected_suffix_shift_no_beep (base : Int → Bool) (gap : Int) (x : Nat)
    (xs : List Nat) (j : Nat) (hj : j < 2 * (UnaryBank.encode (x::xs)).length + 3) :
    ¬ machine.system.BeepFrom
      (cfg 32 (gap+2) (before base gap (UnaryBank.encode (x::xs)))) j :=
  silent_no_beep machine _ _ _ j (selected_suffix_shift base gap x xs) hj

end Shared.Beeping.NPcoNP.NativeHalfSweep
