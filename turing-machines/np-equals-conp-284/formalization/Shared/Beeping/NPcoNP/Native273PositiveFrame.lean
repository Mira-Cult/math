import Shared.Beeping.NPcoNP.Native273Positive

/-! Control frame for the general positive bank operation. -/
namespace Shared.Beeping.NPcoNP.Native273PositiveFrame
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.Native273Positive
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Below the target bank, the positive branch changes exactly the two
control markers. This frame supports subsequent literal control scans. -/
theorem positive_control_frame (h separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (vs : List Nat) (hlen : values.length=10)
    (hlong : h+7≤separator)
    (mark : t (h+2)=true) (z1 : t (h+3)=false) (z2 : t (h+4)=false)
    (ones : ∀ q, h+5≤q → q<separator → t q=true)
    (sep : t separator=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::vs) ++ [false,false]))) :
    let pos := separator+1+((encode values).length : Int)
    let touched := clearAt pos t
    let u := setAt (h+4) (clearAt (h+2) touched)
    let original := setAt pos u
    let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
    let f := pos+2+(suffix.length : Int)
    let out := spec original f (suffix.length+2)
    out (h+2)=false ∧ out (h+3)=false ∧ out (h+4)=true ∧
    (∀ q, h+5≤q → q<separator → out q=true) ∧ out separator=false ∧
    (∀ q, q<pos → q≠h+2 → q≠h+4 → out q=t q) ∧
    Holds out pos (encode (v::vs) ++ [true,false,false]) := by
  dsimp only
  let pos := separator+1+((encode values).length : Int)
  let touched := clearAt pos t
  let u := setAt (h+4) (clearAt (h+2) touched)
  let original := setAt pos u
  let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  let f := pos+2+(suffix.length : Int)
  let out := spec original f (suffix.length+2)
  have hpos : separator+1≤pos := by dsimp [pos]; omega
  have hbelow : ∀ q, q<pos → out q=original q := by
    intro q hq
    apply spec_outside
    left
    dsimp [f]
    push_cast
    omega
  have hframe : ∀ q, q<pos → q≠h+2 → q≠h+4 → out q=t q := by
    intro q hq hn1 hn2
    rw [hbelow q hq]
    simp [original,u,touched,setAt,clearAt,show q≠pos by omega,hn1,hn2]
  have h2 : out (h+2)=false := by
    rw [hbelow _ (by omega)]
    simp [original,u,touched,setAt,clearAt,show h+2≠pos by omega,show h+2≠h+4 by omega]
  have h3 : out (h+3)=false := by rw [hframe _ (by omega) (by omega) (by omega)]; exact z1
  have h4 : out (h+4)=true := by
    rw [hbelow _ (by omega)]
    simp [original,u,setAt,show h+4≠pos by omega]
  have hones : ∀ q, h+5≤q → q<separator → out q=true := by
    intro q hq hq2
    rw [hframe q (by omega) (by omega) (by omega)]
    exact ones q hq hq2
  have hsep : out separator=false := by
    rw [hframe separator (by omega) (by omega) (by omega)]
    exact sep
  have hb := (positive_touch_shift_273 h separator t values v vs hlen hlong mark z1 z2 ones sep bank).1
  exact ⟨h2,h3,h4,hones,hsep,hframe,hb⟩

#print axioms positive_control_frame
end Shared.Beeping.NPcoNP.Native273PositiveFrame
