import Shared.Beeping.NPcoNP.NativeHalfReturnContext
import Shared.Beeping.NPcoNP.NativeHalfReturn23
import Shared.Beeping.NPcoNP.NativeHalfOddReturn
import Shared.Beeping.NPcoNP.NativeHalfSweepShape

/-! Exact return of the literal state-23 scan across a filled selected block
and an encoded left bank. This is a supplied configuration, not reachability. -/
namespace Shared.Beeping.NPcoNP.NativeHalfReturn23BankExact

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfReturn23
open Shared.Beeping.NPcoNP.NativeHalfOddReturn
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Extending an encoded suffix by ones leaves its existing prefix intact. -/
theorem before_append_prefix (back : Int → Bool) (ctrl p : Int)
    (xs ys : List Bool) (hp : p<ctrl+2+(xs.length : Int)) :
    before back ctrl (xs++ys) p=before back ctrl xs p := by
  by_cases h0 : p<ctrl
  · rw [before_prefix _ _ _ _ h0,before_prefix _ _ _ _ h0]
  · by_cases h1 : p<ctrl+2
    · simp [before,h0,h1]
    · let i := (p-ctrl-2).toNat
      have hiint : (i : Int)=p-ctrl-2 := Int.toNat_of_nonneg (by omega)
      have hi : i<xs.length := by omega
      have he : p=ctrl+2+(i : Int) := by omega
      rw [he,before_suffix_bit,before_suffix_bit]
      simp only [bitAt,List.getElem?_append_left hi]

/-- The extra supplied ones occur immediately after the original suffix. -/
theorem before_append_ones (back : Int → Bool) (ctrl p : Int)
    (xs : List Bool) (k : Nat)
    (hp : ctrl+2+(xs.length : Int)≤p)
    (hq : p<ctrl+2+((xs.length+k : Nat) : Int)) :
    before back ctrl (xs++List.replicate k true) p=true := by
  let i := (p-ctrl-2).toNat
  have hiint : (i : Int)=p-ctrl-2 := Int.toNat_of_nonneg (by omega)
  have hi : xs.length ≤ i := by omega
  have hik : i-xs.length<k := by omega
  have he : p=ctrl+2+(i : Int) := by omega
  rw [he,before_suffix_bit]
  simp only [bitAt,List.getElem?_append_right hi]
  simp [List.getElem?_replicate,hik]

/-- A leftward tape pattern transfers when every cell at or left of the
starting head agrees. -/
theorem down_congr (t u : Int → Bool) (h : Int) (xs : List Bool)
    (he : ∀ p≤h, t p=u p) (hu : downHolds u h xs) : downHolds t h xs := by
  induction xs generalizing h with
  | nil => trivial
  | cons x xs ih =>
    change u h=x ∧ downHolds u (h-1) xs at hu
    change t h=x ∧ downHolds t (h-1) xs
    refine ⟨?_,ih (h-1) ?_ hu.2⟩
    · rw [he h (le_refl _)]
      exact hu.1
    · intro p hp
      exact he p (by omega)

/-- The filled selected block and encoded bank form a finite scanner pattern. -/
theorem encoded_filled_pattern (back outBase : Int → Bool) (ctrl b gap : Int)
    (left : List Nat) (word : List Bool) (k : Nat)
    (hb : b=ctrl+2+((leftSuffix left).length : Int))
    (hg : gap=b+(k : Int)-1)
    (hprefix : ∀ p<b, outBase p=before back ctrl (leftSuffix left) p)
    (hfilled : ∀ p, b≤p → p≤gap → outBase p=true) :
    ∃ shape : Shape, (bits shape).length=(leftSuffix left).length+k ∧
      downHolds (after outBase (gap+1) word) gap (bits shape++[false,false]) := by
  let suffix := leftSuffix left ++ List.replicate k true
  let reference := before back ctrl suffix
  let tape := after outBase (gap+1) word
  have heq : ∀ p≤gap, tape p=reference p := by
    intro p hp
    change after outBase (gap+1) word p=before back ctrl suffix p
    rw [after_prefix _ _ _ _ (by omega)]
    by_cases hpb : p<b
    · rw [hprefix p hpb]
      symm
      apply before_append_prefix
      rw [hb] at hpb
      exact hpb
    · have hl : ctrl+2+((leftSuffix left).length : Int)≤p := by rw [← hb]; omega
      have hr : p<ctrl+2+(((leftSuffix left).length+k : Nat) : Int) := by push_cast; omega
      rw [hfilled p (by omega) hp]
      symm
      exact before_append_ones back ctrl p (leftSuffix left) k hl hr
  have hshape : Prefix suffix.reverse := by
    dsimp [suffix,leftSuffix]
    simp only [List.reverse_append,List.reverse_replicate,List.reverse_cons,List.reverse_nil,List.nil_append]
    exact prefix_append (prefix_ones k) (Prefix.one (prefix_reverse_bank left))
  obtain ⟨shape,hshape⟩ := shape_of_prefix suffix.reverse hshape
  have hhead : gap=ctrl+1+(suffix.length : Int) := by dsimp [suffix]; simp; rw [hg,hb]; omega
  have hpat : downHolds reference gap (bits shape++[false,false]) := by
    rw [hshape,hhead]
    exact down_before_reverse back ctrl suffix
  have hpat' : downHolds tape gap (bits shape++[false,false]) := down_congr tape reference gap _ heq hpat
  have hlen : (bits shape).length=(leftSuffix left).length+k := by rw [hshape]; simp [suffix,Nat.add_comm]
  exact ⟨shape,hlen,hpat'⟩

/-- State 23 returns immediately to the left of the header, with unchanged tape. -/
theorem return23_encoded_filled (back outBase : Int → Bool) (ctrl b gap : Int)
    (left : List Nat) (word : List Bool) (k : Nat)
    (hb : b=ctrl+2+((leftSuffix left).length : Int))
    (hg : gap=b+(k : Int)-1)
    (hprefix : ∀ p<b, outBase p=before back ctrl (leftSuffix left) p)
    (hfilled : ∀ p, b≤p → p≤gap → outBase p=true) :
    silentSegment machine (cfg 23 gap (after outBase (gap+1) word))
      (cfg 1 (ctrl-1) (after outBase (gap+1) word))
      ((leftSuffix left).length+k+2) := by
  obtain ⟨shape,hlen,hpat⟩ := encoded_filled_pattern back outBase ctrl b gap left word k hb hg hprefix hfilled
  have hr := return_scan shape gap (after outBase (gap+1) word) hpat
  have hend : gap-((bits shape).length : Int)-2=ctrl-1 := by rw [hlen,hg,hb]; omega
  rw [hend,hlen] at hr
  exact hr

/-- State 25 traverses the same bank and reaches state 95 immediately left
of the header, preserving the whole tape. -/
theorem return25_encoded_filled (back outBase : Int → Bool) (ctrl b gap : Int)
    (left : List Nat) (word : List Bool) (k : Nat)
    (hb : b=ctrl+2+((leftSuffix left).length : Int))
    (hg : gap=b+(k : Int)-1)
    (hprefix : ∀ p<b, outBase p=before back ctrl (leftSuffix left) p)
    (hfilled : ∀ p, b≤p → p≤gap → outBase p=true) :
    silentSegment machine (cfg 25 gap (after outBase (gap+1) word))
      (cfg 95 (ctrl-1) (after outBase (gap+1) word))
      ((leftSuffix left).length+k+2) := by
  obtain ⟨shape,hlen,hpat⟩ := encoded_filled_pattern back outBase ctrl b gap left word k hb hg hprefix hfilled
  have hr := return_scan25 shape gap (after outBase (gap+1) word) hpat
  have hend : gap-((bits shape).length : Int)-2=ctrl-1 := by rw [hlen,hg,hb]; omega
  rw [hend,hlen] at hr
  exact hr

end Shared.Beeping.NPcoNP.NativeHalfReturn23BankExact

#print axioms Shared.Beeping.NPcoNP.NativeHalfReturn23BankExact.return23_encoded_filled

#print axioms Shared.Beeping.NPcoNP.NativeHalfReturn23BankExact.return25_encoded_filled
