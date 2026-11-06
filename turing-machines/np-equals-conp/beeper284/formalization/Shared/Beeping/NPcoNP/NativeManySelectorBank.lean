import Shared.Beeping.NPcoNP.NativeManyWindowBank

/-! Compose the fourteen-block selector entry with its positive window and
complete bank operation. The supplied finite layout is not an all-run invariant. -/
namespace Shared.Beeping.NPcoNP.NativeManySelectorBank
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeManyWindowBank
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

/-- The supplied fourteen-block selector and its preceding marker select
and execute a positive prepared bank in exact finite silent time. -/
theorem selector_to_bank (t : Int → Bool) (a : Int) (k v y w : Nat) (zs vs : List Nat)
    (hl : (List.replicate k 0 ++ (v+3)::y::(w+1)::zs).length=14)
    (marker : t (a-1)=true)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ (v+3)::y::(w+1)::zs)))
    (bank : Holds t (a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+4)
      (encode ((w+1)::vs) ++ [false,false])) :
    let selector := List.replicate k 0 ++ (v+3)::y::(w+1)::zs
    let d := a+((2*k : Nat):Int)+4
    let x := d+(v : Int)+(y : Int)+4
    let u := clearAt d t
    let suffix := List.replicate w true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
    let f := x+2+suffix.length
    let out := spec u f (suffix.length+2)
    Holds out x (encode (w::vs) ++ [true,false,false]) ∧
    (∀ p, p≠d → (p<x ∨ f<p) → out p=t p) ∧
    silentSegment machine (cfg 83 (a+((encode selector).length : Int)-1) t)
      (cfg 23 (x-2) out) ((encode selector).length+1+(2*k+v+y+2*suffix.length+16)) := by
  dsimp only
  let selector := List.replicate k 0 ++ (v+3)::y::(w+1)::zs
  let suffix := List.replicate w true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  have hentry := marker_window_to93 t a selector hl window marker
  obtain ⟨hresult,hframe,hbody⟩ := window_to_bank t a k v y w zs vs window bank
  refine ⟨hresult,hframe,?_⟩
  exact segAdd machine _ _ _ ((encode selector).length+1)
    (2*k+v+y+2*suffix.length+16) hentry hbody

#print axioms selector_to_bank
end Shared.Beeping.NPcoNP.NativeManySelectorBank
