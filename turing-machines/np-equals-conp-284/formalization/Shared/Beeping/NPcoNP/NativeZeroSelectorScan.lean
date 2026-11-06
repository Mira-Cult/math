import Shared.Beeping.NPcoNP.NativeAllZeroSelector
import Shared.Beeping.NPcoNP.NativeAllZeroAbsentExact

/-! A variable-length all-zero selector followed by a supplied zero corridor. -/
namespace Shared.Beeping.NPcoNP.NativeZeroSelectorScan
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeAllZeroSelector
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentExact
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

/-- A supplied `k`-block zero selector dispatches state 261 across a
nonempty finite zero corridor and returns to state 83, with exact time and
tape effect. -/
theorem zero_selector_fill_return (t : Int → Bool) (a : Int) (k len : Nat)
    (hlen : 0<len)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ [0])))
    (marker : t (a+((2*k : Nat):Int)+2)=true)
    (next : t (a+((2*k : Nat):Int)+3)=false)
    (h0 : t (a+((2*k : Nat):Int)+4)=false)
    (h1 : t (a+((2*k : Nat):Int)+5)=false)
    (zeros : ∀ i : Nat, i<len → t (a+((2*k : Nat):Int)+6+(i : Int))=false)
    (stop : t (a+((2*k : Nat):Int)+6+(len : Int))=true) :
    let d := a+((2*k : Nat):Int)+4
    let out := fillRange (setAt d t) (d+2) (d+2+(len : Int))
    silentSegment machine (cfg 93 a t) (cfg 83 (d+(len : Int)) out) (2*k+len+8) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  have hdispatch := all_zero_to261 t a k window marker next
  have hdispatch' : silentSegment machine (cfg 93 a t) (cfg 261 d t) (2*k+4) := by
    simpa only [d] using hdispatch
  have hs := dispatch261_return83_exact len d t hlen (by simpa only [d] using h0)
    (by have hp : d+1=a+((2*k : Nat):Int)+5 := by dsimp [d]; omega
        simpa only [hp] using h1)
    (by intro i hi
        have hp : d+2+(i : Int)=a+((2*k : Nat):Int)+6+(i : Int) := by dsimp [d]; omega
        simpa only [hp] using zeros i hi)
    (by have hp : d+2+(len : Int)=a+((2*k : Nat):Int)+6+(len : Int) := by dsimp [d]; omega
        simpa only [hp] using stop)
  have hall := segAdd machine _ _ _ (2*k+4) (len+4) hdispatch' hs
  have hc : 2*k+4+(len+4)=2*k+len+8 := by omega
  simpa only [hc,d] using hall

#print axioms zero_selector_fill_return
end Shared.Beeping.NPcoNP.NativeZeroSelectorScan
