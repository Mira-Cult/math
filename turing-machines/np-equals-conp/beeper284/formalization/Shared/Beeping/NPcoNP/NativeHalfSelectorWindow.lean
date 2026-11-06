import Shared.Beeping.NPcoNP.NativeHalfSelectorExact
import Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

/-! Exact selector behavior for a finite bank window on an arbitrary tape.
In contrast to the isolated before-tape fixture, this permits arbitrary
additional registers or control data on either side of the specified word. -/
namespace Shared.Beeping.NPcoNP.NativeHalfSelectorWindow

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- A forward finite word can be read backwards without constraining the
rest of the two-sided tape. -/
theorem holds_reverse (t : Int → Bool) (a : Int) (xs : List Bool)
    (hx : Holds t a xs) :
    downHolds t (a+(xs.length : Int)-1) xs.reverse := by
  apply down_of_get
  intro i hi
  have hi' : i<xs.length := by simpa using hi
  rw [List.getElem_reverse]
  have hj : xs.length-1-i<xs.length := by omega
  have he : a+(xs.length : Int)-1-(i : Int)=a+((xs.length-1-i : Nat) : Int) := by omega
  rw [he]
  exact holds_get t a xs hx _ hj

/-- A window consisting of a separator and fourteen encoded values is
scanned in reverse value order, with exact duration and full tape unchanged. -/
theorem selector_window_to92 (t : Int → Bool) (a : Int) (xs : List Nat)
    (hl : xs.length=14) (hx : Holds t a (false :: encode xs)) :
    silentSegment machine (cfg 83 (a+((encode xs).length : Int)-1) t)
      (cfg 92 (a-1) t) (encode xs).length := by
  have hr := holds_reverse t a (false :: encode xs) hx
  have he : (false :: encode xs).reverse = false :: encode xs.reverse := by
    simpa using encode_reverse xs
  rw [he] at hr
  have hd : downHolds t (a+((encode xs).length : Int)-1) (encode xs.reverse) := by
    have hp : a+(((false :: encode xs).length : Nat) : Int)-1-1 =
        a+((encode xs).length : Int)-1 := by simp only [List.length_cons, Nat.cast_succ]; omega
    have hr' := hr.2
    rw [hp] at hr'
    exact hr'
  have hd' : downHolds t (a+((encode xs).length : Int)-1) (encode xs.reverse ++ []) := by
    simpa using hd
  have hs := (selector_on_values xs.reverse _ t [] (by simpa using hl) hd').2
  have hlen := encode_length_reverse xs
  rw [hlen] at hs
  have hpos : a+((encode xs).length : Int)-1-((encode xs).length : Int)=a-1 := by omega
  rw [hpos] at hs
  exact hs

/-- If the cell just left of the window is one, the final rightward scan
immediately returns to state 93 at the window's separator. -/
theorem selector_window_to93 (t : Int → Bool) (a : Int) (xs : List Nat)
    (hl : xs.length=14) (hx : Holds t a (false :: encode xs))
    (hm : t (a-1)=true) :
    silentSegment machine (cfg 83 (a+((encode xs).length : Int)-1) t)
      (cfg 93 a t) ((encode xs).length+1) := by
  have hs := selector_window_to92 t a xs hl hx
  have hr := oneSeg machine _ _ (step92_one (a-1) t hm)
  have h := segAdd machine _ _ _ (encode xs).length 1 hs hr
  simpa using h

end Shared.Beeping.NPcoNP.NativeHalfSelectorWindow

#print axioms Shared.Beeping.NPcoNP.NativeHalfSelectorWindow.selector_window_to92
#print axioms Shared.Beeping.NPcoNP.NativeHalfSelectorWindow.selector_window_to93
