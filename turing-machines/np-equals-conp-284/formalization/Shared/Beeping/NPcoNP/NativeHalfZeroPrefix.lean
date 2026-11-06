import Shared.Beeping.NPcoNP.NativeHalfSuffixShift
namespace Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.Table284

theorem prefix_tail_unary (x : Nat) (xs : List Nat) :
    Prefix (List.replicate x true ++ xs.flatMap (fun z => false :: List.replicate (z+1) true)) := by
  apply prefix_append (prefix_ones x)
  induction xs with
  | nil => exact .nil
  | cons z zs ih =>
    simp only [List.flatMap_cons]
    apply prefix_append
    · simpa [List.replicate_succ] using (Prefix.zeroOne (prefix_ones z))
    · exact ih

theorem prefix_zero_unary (x : Nat) (xs : List Nat) : Prefix (false :: unaryBankPrefix x xs) := by
  simp only [unaryBankPrefix, List.replicate_succ, List.cons_append]
  exact Prefix.zeroOne (prefix_tail_unary x xs)

theorem selected_before_zero_bank (base : Int → Bool) (gap : Int) (values : List Nat) :
    let suffix := false :: UnaryBank.encode values
    silentSegment machine (cfg 32 (gap+2) (before base gap suffix))
      (cfg 34 (gap+1+suffix.length) (before base gap suffix)) (suffix.length+1) := by
  cases values with
  | nil =>
    have ht : Holds (before base gap [false]) (gap+2) ([] ++ [false,false]) := by
      simpa using holds_before_suffix base gap [false]
    have h := selected_scan [] Prefix.nil (gap+2) (before base gap [false]) ht
    change silentSegment machine (cfg 32 (gap+2) (before base gap [false]))
      (cfg 34 (gap+1+1) (before base gap [false])) 2
    have hh : gap+1+1 = gap+2 := by omega
    rw [hh]
    simpa using h
  | cons x xs =>
    let suffix := false :: UnaryBank.encode (x::xs)
    let pre := false :: unaryBankPrefix x xs
    have he : pre ++ [false,false] = suffix ++ [false] := by
      dsimp [pre,suffix]
      simp only [bank_prefix_identity]
    have ht : Holds (before base gap suffix) (gap+2) (pre ++ [false,false]) := by
      rw [he]
      exact holds_before_suffix base gap suffix
    have hp : Prefix pre := prefix_zero_unary x xs
    have h := selected_scan pre hp (gap+2) (before base gap suffix) ht
    have hl := Shared.Beeping.NPcoNP.NativeHalfSweep.prefix_length x xs
    have hehead : gap+2+(pre.length : Int) = gap+1+(suffix.length : Int) := by
      dsimp [pre,suffix]; omega
    have helen : pre.length+2 = suffix.length+1 := by
      dsimp [pre,suffix]; omega
    rw [hehead, helen] at h
    exact h
end Shared.Beeping.NPcoNP.NativeHalfScan


namespace Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.Table284

/-- A redundant zero preceding the moved suffix may be left untouched. -/
theorem spec_redundant_zero (t : Int → Bool) (h : Int) (k : Nat)
    (h0 : t (h-(k:Int)) = false) (h1 : t (h-(k:Int)-1) = false) :
    spec t h k = spec t h (k+1) := by
  funext i
  by_cases he : i = h-(k:Int)-1
  · subst i
    have hne : h-(k:Int)-1 ≠ h := by omega
    have hno : ¬ (h-(k:Int) ≤ h-(k:Int)-1 ∧ h-(k:Int)-1 < h) := by omega
    have hyes : h-((k:Int)+1) ≤ h-(k:Int)-1 ∧ h-(k:Int)-1 < h := by omega
    have haddr : h-(k:Int)-1+1 = h-(k:Int) := by omega
    simp [spec, Nat.cast_add, hne, hyes, haddr, h0, h1]
  · by_cases hh : i = h
    · subst i; simp [spec]
    · have hequiv : (h-(k:Int) ≤ i ∧ i < h) ↔ (h-((k:Int)+1) ≤ i ∧ i < h) := by omega
      simp only [spec, Nat.cast_add, Nat.cast_one, if_neg hh]
      simp only [hequiv]

/-- The two zero gaps make a leading zero of the suffix redundant to the sweep. -/
theorem down_before_leading_zero (base : Int → Bool) (gap : Int) (suffix : List Bool) :
    downHolds (before base gap (false::suffix)) (gap+2+suffix.length)
      (suffix.reverse ++ [false,false]) := by
  apply down_of_get
  intro i hi
  by_cases h : i < suffix.length
  · have hr : i < suffix.reverse.length := by simpa using h
    rw [List.getElem_append_left hr, List.getElem_reverse]
    have hj : suffix.length - 1 - i < suffix.length := by omega
    have he : gap+2+(suffix.length : Int) - (i : Int) = gap+2+((1+(suffix.length-1-i) : Nat) : Int) := by omega
    rw [he, before_suffix_bit]
    simp only [bitAt]
    have hz : 1 + (suffix.length-1-i) = (suffix.length-1-i) + 1 := by omega
    rw [hz]
    simp [List.getElem?_eq_getElem hj]
  · have hib : i < suffix.length + 2 := by simpa using hi
    have he : i = suffix.length ∨ i = suffix.length+1 := by omega
    rcases he with h0 | h1
    · subst i
      have heq : gap+2+(suffix.length : Int) - (suffix.length : Int) = gap+2 := by omega
      rw [heq]
      simp [before, bitAt]
    · subst i
      have heq : gap+2+(suffix.length : Int) - ((suffix.length+1 : Nat) : Int) = gap+1 := by omega
      rw [heq]
      simp [before]

theorem spec_before_leading_zero (base : Int → Bool) (gap : Int) (suffix : List Bool) :
    spec (before base gap (false::suffix)) (gap+2+suffix.length) suffix.length =
      after base gap (false::suffix) := by
  let tape := before base gap (false::suffix)
  let h : Int := gap+2+suffix.length
  have h0 : tape (h-(suffix.length:Int)) = false := by
    dsimp [tape, h]; simp [before, bitAt]
  have h1 : tape (h-(suffix.length:Int)-1) = false := by
    dsimp [tape, h]; simp [before]
  have hs := spec_redundant_zero tape h suffix.length h0 h1
  rw [hs]
  have hc := spec_before_eq_after base gap (false::suffix)
  have heq : gap + 1 + ((suffix.length : Int) + 1) = gap + 2 + suffix.length := by omega
  simpa [tape, h, heq] using hc

/-- Complete backward sweep for the zero-prefixed case. -/
theorem selected_zero_prefix_sweep (base : Int → Bool) (gap : Int) (xs : List Nat) :
    let suffix := UnaryBank.encode xs
    let full := false::suffix
    silentSegment machine
      (cfg 34 (gap+2+suffix.length) (before base gap full))
      (cfg 31 gap (after base gap full)) (suffix.length+2) := by
  dsimp only
  let suffix := UnaryBank.encode xs
  obtain ⟨s, hs⟩ := shape_reverse_bank xs
  have hd := down_before_leading_zero base gap suffix
  have hd' : downHolds (before base gap (false::suffix)) (gap+2+suffix.length) (bits s ++ [false,false]) := by
    simpa [suffix, hs] using hd
  have hl : (bits s).length = suffix.length := by simpa [suffix, hs]
  have h := sweep_spec s (gap+2+suffix.length) (before base gap (false::suffix)) hd'
  rw [hl, spec_before_leading_zero] at h
  have hp : gap+2+(suffix.length:Int)-(suffix.length:Int)-2 = gap := by omega
  rw [hp] at h
  simpa only [suffix] using h
end Shared.Beeping.NPcoNP.NativeHalfSweep

namespace Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Table284

/-- A prepared zero-prefixed suffix is scanned and shifted silently by the
literal machine. No reachability or complete HALF correctness is claimed. -/
theorem selected_zero_prefix_shift (base : Int → Bool) (gap : Int) (values : List Nat) :
    let full := false :: UnaryBank.encode values
    silentSegment machine
      (cfg 32 (gap+2) (before base gap full))
      (cfg 31 gap (after base gap full)) (2*full.length+2) := by
  dsimp only
  let suffix := UnaryBank.encode values
  have hscan := selected_before_zero_bank base gap values
  have hscan' : silentSegment machine
      (cfg 32 (gap+2) (before base gap (false::suffix)))
      (cfg 34 (gap+2+suffix.length) (before base gap (false::suffix)))
      (suffix.length+2) := by
    have hp : gap+1+((false::suffix).length : Int) = gap+2+suffix.length := by simp; omega
    have ht : (false::suffix).length+1 = suffix.length+2 := by simp
    change silentSegment machine
      (cfg 32 (gap+2) (before base gap (false::suffix)))
      (cfg 34 (gap+1+(false::suffix).length) (before base gap (false::suffix)))
      ((false::suffix).length+1) at hscan
    rw [hp, ht] at hscan
    exact hscan
  have hsweep := selected_zero_prefix_sweep base gap values
  change silentSegment machine
      (cfg 34 (gap+2+suffix.length) (before base gap (false::suffix)))
      (cfg 31 gap (after base gap (false::suffix))) (suffix.length+2) at hsweep
  have hh := segAdd machine _ _ _ (suffix.length+2) (suffix.length+2) hscan' hsweep
  dsimp only [suffix] at hh
  convert hh using 1 <;> simp <;> omega

theorem selected_zero_prefix_shift_positive (values : List Nat) :
    0 < 2*(false :: UnaryBank.encode values).length+2 := by omega

theorem selected_zero_prefix_shift_no_beep (base : Int → Bool) (gap : Int)
    (values : List Nat) (j : Nat)
    (hj : j < 2*(false :: UnaryBank.encode values).length+2) :
    ¬ machine.system.BeepFrom
      (cfg 32 (gap+2) (before base gap (false :: UnaryBank.encode values))) j :=
  silent_no_beep machine _ _ _ j (selected_zero_prefix_shift base gap values) hj
end Shared.Beeping.NPcoNP.NativeHalfSweep
