import Shared.Beeping.NPcoNP.NativeZeroWindowGeneric

/-! The common reverse/forward scan needs one blank after the scanned bank,
not a blank at the next cell. The latter may be the second one of a positive
unary target. The temporary shadow tape is used only in the proof. -/
namespace Shared.Beeping.NPcoNP.NativeOneBlankWindow
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeZeroWindowGeneric
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- A descending word depends only on cells at or below its starting head. -/
theorem down_transport_below (t u : Int → Bool) (h : Int) (xs : List Bool)
    (word : downHolds t h xs) (frame : ∀ q, q≤h → t q=u q) :
    downHolds u h xs := by
  induction xs generalizing h with
  | nil => trivial
  | cons b xs ih =>
    change t h=b ∧ downHolds t (h-1) xs at word
    change u h=b ∧ downHolds u (h-1) xs
    exact ⟨(frame h (by omega)).symm.trans word.1,
      ih (h-1) word.2 (by intro q hq; exact frame q (by omega))⟩

/-- Finite windows to and from a touched target. No condition is imposed on
the cell immediately after the touched target. -/
theorem one_blank_windows_min_gap (h separator : Int) (t : Int → Bool) (values : List Nat)
    (hlong : h+6≤separator)
    (hz1 : t (h+3)=false) (hz2 : t (h+4)=false)
    (ones : ∀ q, h+5≤q → q<separator → t q=true)
    (hsep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ [false])) :
    let r := (separator-(h+6)).toNat
    let ys := unaryBankPrefix r values
    let pos := separator+1+((encode values).length : Int)
    Prefix ys ∧ Prefix ys.reverse ∧
      downHolds t (pos-2) (ys.reverse ++ [false,false]) ∧
      Holds t (h+5) (ys ++ [false,false]) ∧
      pos=(h+2)+(ys.length : Int)+4 := by
  dsimp only
  let r := (separator-(h+6)).toNat
  let ys := unaryBankPrefix r values
  let pos := separator+1+((encode values).length : Int)
  let u := clearAt (pos+1) t
  have hpos : separator+1≤pos := by dsimp [pos]; omega
  have hf : ∀ q, q≤pos → u q=t q := by
    intro q hq
    simp [u,clearAt,show q≠pos+1 by omega]
  have hu1 : u (h+3)=false := by rw [hf _ (by omega)]; exact hz1
  have hu2 : u (h+4)=false := by rw [hf _ (by omega)]; exact hz2
  have huones : ∀ q, h+5≤q → q<separator → u q=true := by
    intro q hq hq2
    rw [hf _ (by omega)]
    exact ones q hq hq2
  have husep : u separator=false := by rw [hf _ (by omega)]; exact hsep
  have hprefix : Holds t (separator+1) (encode values) :=
    holds_prefix_word t (separator+1) (encode values) [false] bank
  have hprefix' : Holds u (separator+1) (encode values) := by
    apply holds_transport t u _ _ hprefix
    intro q hq hq2
    exact (hf q (by dsimp [pos] at *; omega)).symm
  have hlast := holds_append_tail t (separator+1) (encode values) [false] bank
  have hzpos : t pos=false := by simpa [pos,Holds] using hlast.1
  have htail : Holds u pos [false,false] := by
    simp [Holds,u,clearAt,show pos≠pos+1 by omega,hzpos]
  have hbank : Holds u (separator+1) (encode values ++ [false,false]) := by
    apply holds_append_intro u (separator+1) (encode values) [false,false] hprefix'
    simpa only [pos] using htail
  obtain ⟨hy,hx,hleft,hright,hposition⟩ :=
    zero_windows_generic_min_gap h separator u values hlong hu1 hu2 huones husep hbank
  change pos=(h+2)+(ys.length : Int)+4 at hposition
  have hleft' : downHolds t (pos-2) (ys.reverse ++ [false,false]) := by
    apply down_transport_below u t (pos-2) _ hleft
    intro q hq
    exact hf q (by omega)
  have hright' : Holds t (h+5) (ys ++ [false,false]) := by
    have hr : Holds u (h+5) (ys ++ [false,false]) := by
      apply holds_prefix_word u (h+5) (ys ++ [false,false]) [false]
      simpa [List.append_assoc] using hright
    apply holds_transport u t _ _ hr
    intro q hq hq2
    apply hf q
    simp only [List.length_append,List.length_cons,List.length_nil,Nat.cast_add,Nat.cast_ofNat] at hq2
    omega
  exact ⟨hy,hx,hleft',hright',hposition⟩

theorem one_blank_windows (h separator : Int) (t : Int → Bool) (values : List Nat)
    (hlong : h+7≤separator)
    (hz1 : t (h+3)=false) (hz2 : t (h+4)=false)
    (ones : ∀ q, h+5≤q → q<separator → t q=true)
    (hsep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ [false])) :
    let r := (separator-(h+6)).toNat
    let ys := unaryBankPrefix r values
    let pos := separator+1+((encode values).length : Int)
    Prefix ys ∧ Prefix ys.reverse ∧
      downHolds t (pos-2) (ys.reverse ++ [false,false]) ∧
      Holds t (h+5) (ys ++ [false,false]) ∧
      pos=(h+2)+(ys.length : Int)+4 := by
  exact one_blank_windows_min_gap h separator t values (by omega) hz1 hz2 ones hsep bank

#print axioms down_transport_below
#print axioms one_blank_windows_min_gap
#print axioms one_blank_windows
end Shared.Beeping.NPcoNP.NativeOneBlankWindow
