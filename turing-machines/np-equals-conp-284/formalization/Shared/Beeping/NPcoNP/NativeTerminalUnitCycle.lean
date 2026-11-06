import Shared.Beeping.NPcoNP.NativeTerminalUnitSelector

/-! Exact state-83 to state-83 return for a terminal unit selector. -/
namespace Shared.Beeping.NPcoNP.NativeTerminalUnitCycle
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeTerminalUnitSelector
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- The selector, terminal-marker branch, and state-10 fill return form a
finite silent segment. The supplied right marker prevents a silent stall. -/
theorem terminal_unit_cycle (t : Int → Bool) (a : Int) (z k : Nat)
    (hk : 0<k) (hl : (List.replicate z 0 ++ [1]).length=14)
    (window : Holds t a (markerWindow (List.replicate z 0 ++ [1])))
    (left : t (a-1)=true)
    (marker : t (a+((2*z : Nat):Int)+3)=true)
    (h0 : t (a+((2*z : Nat):Int)+4)=false)
    (h1 : t (a+((2*z : Nat):Int)+5)=false)
    (hz : ∀ i : Nat, i<k → t (a+((2*z : Nat):Int)+6+(i : Int))=false)
    (hm : t (a+((2*z : Nat):Int)+6+(k : Int))=true) :
    let d := a+((2*z : Nat):Int)+4
    let out := fillRange (setAt d t) (d+2) (d+2+(k : Int))
    silentSegment machine (cfg 83 (a+((2*z : Nat):Int)+2) t)
      (cfg 83 (d+(k : Int)) out) (4*z+k+12) := by
  dsimp only
  let xs := List.replicate z 0 ++ [1]
  have hlen : (encode xs).length=2*z+3 := by
    dsimp [xs]
    simp [encode_append,encode,block_length,zeros_length]
  have hselect := marker_window_to93 t a xs hl window left
  have hstart : a+(((encode xs).length : Nat):Int)-1=a+((2*z : Nat):Int)+2 := by rw [hlen]; push_cast; omega
  have hcost : (encode xs).length+1=2*z+4 := by rw [hlen]
  rw [hstart,hcost] at hselect
  have hfill := terminal_unit_fill_return t a z k hk window marker h0 h1 hz hm
  have hall := segAdd machine _ _ _ (2*z+4) (2*z+k+8) hselect hfill
  have he : 2*z+4+(2*z+k+8)=4*z+k+12 := by omega
  simpa only [he] using hall

#print axioms terminal_unit_cycle
end Shared.Beeping.NPcoNP.NativeTerminalUnitCycle
