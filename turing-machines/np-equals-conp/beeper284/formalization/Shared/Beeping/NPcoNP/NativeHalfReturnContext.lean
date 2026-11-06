import Shared.Beeping.NPcoNP.NativeHalfEntryCorrect
import Shared.Beeping.NPcoNP.NativeHalfState1Layout

/-! Unary-bank prefix facts for a native-HALF return. They use a supplied
header gap and do not establish graph-entry reachability. -/
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.NativeHalfPrefixNo00
open Shared.Beeping.NPcoNP.NativeHalfScan

/-- Two neighboring zeros cannot occur in a `Prefix` word. -/
theorem prefix_no00 (xs : List Bool) (hx : Prefix xs) :
    ∀ i : Nat, (hi : i+1<xs.length) → xs[i]'(by omega)=false → xs[i+1]'hi=true := by
  induction hx with
  | nil => intro i hi; simp at hi
  | @one xs hx ih =>
    intro i hi hz
    cases i with
    | zero => simp at hz
    | succ i =>
      have hi' : i+1<xs.length := by simp at hi; omega
      have hz' : xs[i]'(by omega)=false := by simpa using hz
      have hh := ih i hi' hz'
      simpa using hh
  | @zeroOne xs hx ih =>
    intro i hi hz
    cases i with
    | zero => simp
    | succ i =>
      cases i with
      | zero => simp at hz
      | succ i =>
        have hi' : i+1<xs.length := by simp at hi; omega
        have hz' : xs[i]'(by omega)=false := by simpa using hz
        have hh := ih i hi' hz'
        simpa using hh
end Shared.Beeping.NPcoNP.NativeHalfPrefixNo00

namespace Shared.Beeping.NPcoNP.NativeHalfPrefixNo00
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfCleanupScan
open Shared.Beeping.NPcoNP.NativeHalfOddCleanupScan
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

theorem before_bank_no00 (back : Int → Bool) (gap : Int) (left : List Nat) (p : Int)
    (hp : gap+1≤p) (hq : p<gap+1+((leftSuffix left).length : Int))
    (hz : before back gap (leftSuffix left) p=false) :
    before back gap (leftSuffix left) (p+1)=true := by
  let suffix := leftSuffix left
  let t := before back gap suffix
  change p<gap+1+(suffix.length : Int) at hq
  by_cases he : p=gap+1
  · subst p
    have h := before_suffix_bit back gap suffix 0
    have hf : bitAt suffix 0=true := suffix_first left
    have hc : gap+2+((0 : Nat) : Int)=gap+1+1 := by omega
    rw [hc,hf] at h
    exact h
  · have hp' : gap+2≤p := by omega
    let i := (p-gap-2).toNat
    have hiint : (i : Int)=p-gap-2 := by dsimp [i]; exact Int.toNat_of_nonneg (by omega)
    have hi : i+1<suffix.length := by omega
    have hc : gap+2+(i : Int)=p := by omega
    have hc' : gap+2+((i+1 : Nat) : Int)=p+1 := by push_cast; omega
    have h0 := before_suffix_bit back gap suffix i
    have h1 := before_suffix_bit back gap suffix (i+1)
    rw [hc] at h0
    rw [hc'] at h1
    have hbit0 : suffix[i]'(by omega)=false := by
      rw [hz] at h0
      have hii : i<suffix.length := by omega
      simpa only [bitAt,List.getElem?_eq_getElem hii,Option.getD_some] using h0.symm
    have hprefix : Prefix suffix := by
      change Prefix (encode left ++ [true])
      exact prefix_tail_of_zero (prefix_zero_encoded left)
    have hbit1 := prefix_no00 suffix hprefix i hi hbit0
    rw [h1]
    simpa only [bitAt,List.getElem?_eq_getElem hi,Option.getD_some] using hbit1

end Shared.Beeping.NPcoNP.NativeHalfPrefixNo00

namespace Shared.Beeping.NPcoNP.NativeHalfPrefixNo00
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

theorem before_selected_one (back : Int → Bool) (gap : Int) (left : List Nat) :
    before back gap (leftSuffix left) (gap+1+((leftSuffix left).length : Int))=true := by
  have hb := before_suffix_bit back gap (leftSuffix left) (encode left).length
  have hc : gap+2+(((encode left).length : Nat) : Int) =
      gap+1+((leftSuffix left).length : Int) := by simp [leftSuffix]; omega
  rw [hc] at hb
  have hv : bitAt (leftSuffix left) (encode left).length=true := by
    simp [leftSuffix,bitAt]
  rw [hv] at hb
  exact hb

/-- No pair of zeros lies between the header gap and the end of the
filled selected block. -/
theorem output_no00 (back outBase : Int → Bool) (ctrl b gap : Int) (left : List Nat)
    (word : List Bool) (hb : b=ctrl+2+((leftSuffix left).length : Int)) (hbg : b-1≤gap)
    (hprefix : ∀ p<b, outBase p=before back ctrl (leftSuffix left) p)
    (hfilled : ∀ p, b≤p → p≤gap → outBase p=true) :
    ∀ p, ctrl+1≤p → p<gap → after outBase (gap+1) word p=false →
      after outBase (gap+1) word (p+1)=true := by
  intro p hp hpg hz
  have hp0 : p<gap+1 := by omega
  have hp1 : p+1<gap+1 := by omega
  rw [after_prefix _ _ _ _ hp0] at hz
  rw [after_prefix _ _ _ _ hp1]
  by_cases hleft : p<b-1
  · have hp'b : p<b := by omega
    have hp1b : p+1<b := by omega
    rw [hprefix _ hp'b] at hz
    rw [hprefix _ hp1b]
    apply before_bank_no00 back ctrl left p hp ?_ hz
    rw [hb] at hleft
    omega
  · have hbp : b-1≤p := by omega
    by_cases he : p=b-1
    · subst p
      have hbase : before back ctrl (leftSuffix left) (b-1)=true := by
        rw [hb]
        have hh := before_selected_one back ctrl left
        have hc : ctrl+2+((leftSuffix left).length : Int)-1=ctrl+1+((leftSuffix left).length : Int) := by omega
        rw [hc]
        exact hh
      rw [hprefix _ (by omega),hbase] at hz
      contradiction
    · have hpb : b≤p := by omega
      rw [hfilled _ hpb (by omega)] at hz
      contradiction

end Shared.Beeping.NPcoNP.NativeHalfPrefixNo00

namespace Shared.Beeping.NPcoNP.NativeHalfPrefixNo00
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.UnarySuffixShift

/-- The odd return's double-zero marker must lie at or left of the header:
the bank and filled selected block contain no adjacent zeros. -/
theorem odd_head_before_header (back outBase : Int → Bool) (ctrl b gap head : Int)
    (left : List Nat) (word : List Bool)
    (hb : b=ctrl+2+((leftSuffix left).length : Int)) (hbg : b≤gap)
    (hprefix : ∀ p<b, outBase p=before back ctrl (leftSuffix left) p)
    (hfilled : ∀ p, b≤p → p≤gap → outBase p=true)
    (hhead : head<gap)
    (hz0 : after outBase (gap+1) word (head+1)=false)
    (hz1 : after outBase (gap+1) word (head+2)=false) : head<ctrl := by
  by_contra hn
  have hp : ctrl+1≤head+1 := by omega
  by_cases he : head+1=gap
  · have ht : after outBase (gap+1) word gap=true := by
      rw [after_prefix _ _ _ _ (by omega)]
      exact hfilled gap hbg (le_refl _)
    rw [he,ht] at hz0
    contradiction
  · have hlt : head+1<gap := by omega
    have ht := output_no00 back outBase ctrl b gap left word hb (by omega) hprefix hfilled
      (head+1) hp hlt hz0
    have hc : head+1+1=head+2 := by omega
    rw [hc] at ht
    rw [ht] at hz1
    contradiction

/-- The same bound also covers a zero selected value, where the selected
block ends immediately before `b` and there is no filled extension. -/
theorem return_head_before_header (back outBase : Int → Bool) (ctrl b gap head : Int)
    (left : List Nat) (word : List Bool)
    (hb : b=ctrl+2+((leftSuffix left).length : Int)) (hbg : b-1≤gap)
    (hprefix : ∀ p<b, outBase p=before back ctrl (leftSuffix left) p)
    (hselected : outBase (b-1)=true)
    (hfilled : ∀ p, b≤p → p≤gap → outBase p=true)
    (hhead : head<gap)
    (hz0 : after outBase (gap+1) word (head+1)=false)
    (hz1 : after outBase (gap+1) word (head+2)=false) : head<ctrl := by
  by_contra hn
  have hp : ctrl+1≤head+1 := by omega
  by_cases he : head+1=gap
  · have ht : after outBase (gap+1) word gap=true := by
      rw [after_prefix _ _ _ _ (by omega)]
      by_cases hb' : b≤gap
      · exact hfilled gap hb' (le_refl _)
      · have hgap : gap=b-1 := by omega
        rw [hgap]
        exact hselected
    rw [he,ht] at hz0
    contradiction
  · have hlt : head+1<gap := by omega
    have ht := output_no00 back outBase ctrl b gap left word hb hbg hprefix hfilled
      (head+1) hp hlt hz0
    have hc : head+1+1=head+2 := by omega
    rw [hc] at ht
    rw [ht] at hz1
    contradiction
end Shared.Beeping.NPcoNP.NativeHalfPrefixNo00

#print axioms Shared.Beeping.NPcoNP.NativeHalfPrefixNo00.odd_head_before_header
#print axioms Shared.Beeping.NPcoNP.NativeHalfPrefixNo00.return_head_before_header
