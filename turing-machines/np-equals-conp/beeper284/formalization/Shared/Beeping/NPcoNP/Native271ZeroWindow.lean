import Shared.Beeping.NPcoNP.NativeZeroRestoreWindow

/-! Zero-restoration windows when the target is the first bank block. -/
namespace Shared.Beeping.NPcoNP.Native271ZeroWindow
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeZeroRestoreWindow
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- A filled control run followed immediately by the temporarily cleared
first zero block supplies both scan windows and their common length. -/
theorem zero_windows_first (h separator : Int) (t : Int → Bool)
    (hlong : h+7≤separator)
    (hz1 : t (h+3)=false) (hz2 : t (h+4)=false)
    (ones : ∀ q, h+5≤q → q<separator → t q=true)
    (hsep : t separator=false) (target : Holds t (separator+1) [false,false]) :
    let k := (separator-(h+5)).toNat
    let ys := List.replicate k true
    Prefix ys ∧ Prefix ys.reverse ∧
      downHolds t (separator-1) (ys.reverse ++ [false,false]) ∧
      Holds t (h+5) (ys ++ [false,false,false]) ∧
      separator+1=(h+2)+(ys.length : Int)+4 := by
  dsimp only
  let k := (separator-(h+5)).toNat
  let ys := List.replicate k true
  have hk : (k : Int)=separator-(h+5) := Int.toNat_of_nonneg (by omega)
  have hc : Holds t (h+5) ys := by
    apply holds_ones
    intro i hi
    apply ones <;> omega
  have htail : Holds t separator [false,false,false] := by
    change t separator=false ∧ Holds t (separator+1) [false,false]
    exact ⟨hsep,target⟩
  have hall := holds_append_intro t (h+5) ys [false,false,false] hc (by
    have he : h+5+(ys.length : Int)=separator := by simp [ys]; omega
    simpa only [he] using htail)
  have hy : Prefix ys := prefix_ones k
  have hx : Prefix ys.reverse := by simpa [ys] using hy
  have hleft : Holds t (h+3) ([false,false] ++ ys) := by
    change t (h+3)=false ∧ t (h+3+1)=false ∧ Holds t (h+3+1+1) ys
    have he1 : h+3+1=h+4 := by omega
    have he2 : h+3+1+1=h+5 := by omega
    have he3 : h+4+1=h+5 := by omega
    simpa only [he1,he2,he3] using And.intro hz1 (And.intro hz2 hc)
  have hreverse := holds_reverse t (h+3) ([false,false] ++ ys) hleft
  have hstart : h+3+((([false,false] ++ ys).length : Nat) : Int)-1=separator-1 := by
    simp only [List.length_append,List.length_cons,List.length_nil,ys,List.length_replicate,Nat.cast_add,Nat.cast_ofNat]
    omega
  have hreverse' : downHolds t (separator-1) (ys.reverse ++ [false,false]) := by
    have he : ([false,false] ++ ys).reverse=ys.reverse ++ [false,false] := by simp
    rw [hstart,he] at hreverse
    exact hreverse
  refine ⟨hy,hx,hreverse',hall,?_⟩
  simp only [ys,List.length_replicate]
  omega

#print axioms zero_windows_first
end Shared.Beeping.NPcoNP.Native271ZeroWindow
