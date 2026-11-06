import Shared.Beeping.NPcoNP.Native273ZeroRestore

/-! Control frame for the general zero-target bank operation. -/
namespace Shared.Beeping.NPcoNP.Native273ZeroFrame
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.Native273ZeroRestore
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Below the target bank, the zero branch changes exactly the two control
markers. The target and the complete bank suffix are restored. -/
theorem zero_control_frame (h separator : Int) (t : Int → Bool)
    (values : List Nat) (tail : List Bool) (hlen : values.length=10)
    (hlong : h+7≤separator)
    (mark : t (h+2)=true) (z1 : t (h+3)=false) (z2 : t (h+4)=false)
    (ones : ∀ q, h+5≤q → q<separator → t q=true)
    (sep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ (block 0 ++ tail))) :
    let pos := separator+1+((encode values).length : Int)
    let touched := clearAt pos t
    let out := setAt pos (setAt (h+4) (clearAt (h+2) touched))
    out (h+2)=false ∧ out (h+3)=false ∧ out (h+4)=true ∧
    (∀ q, h+5≤q → q<separator → out q=true) ∧ out separator=false ∧
    (∀ q, q<pos → q≠h+2 → q≠h+4 → out q=t q) ∧
    (∀ q, separator≤q → out q=t q) := by
  dsimp only
  let pos := separator+1+((encode values).length : Int)
  let touched := clearAt pos t
  let out := setAt pos (setAt (h+4) (clearAt (h+2) touched))
  have hpos : separator+1≤pos := by dsimp [pos]; omega
  have hframe : ∀ q, q<pos → q≠h+2 → q≠h+4 → out q=t q := by
    intro q hq hn1 hn2
    simp [out,touched,setAt,clearAt,show q≠pos by omega,hn1,hn2]
  have h2 : out (h+2)=false := by
    simp [out,touched,setAt,clearAt,show h+2≠pos by omega,show h+2≠h+4 by omega]
  have h3 : out (h+3)=false := by rw [hframe _ (by omega) (by omega) (by omega)]; exact z1
  have h4 : out (h+4)=true := by simp [out,setAt,show h+4≠pos by omega]
  have hones : ∀ q, h+5≤q → q<separator → out q=true := by
    intro q hq hq2
    rw [hframe q (by omega) (by omega) (by omega)]
    exact ones q hq hq2
  have hsep : out separator=false := by
    rw [hframe separator (by omega) (by omega) (by omega)]
    exact sep
  have hsuffix := (zero_touch_restore_273 h separator t values tail hlen hlong mark z1 z2 ones sep bank).1
  exact ⟨h2,h3,h4,hones,hsep,hframe,hsuffix⟩

#print axioms zero_control_frame
end Shared.Beeping.NPcoNP.Native273ZeroFrame
