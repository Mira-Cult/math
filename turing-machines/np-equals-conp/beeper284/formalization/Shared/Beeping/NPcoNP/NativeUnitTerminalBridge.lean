import Shared.Beeping.NPcoNP.NativeUnitTerminalBridgeExact
import Shared.Beeping.NPcoNP.NativeUnit261Cycle83
import Shared.Beeping.NPcoNP.NativeTerminalUnitCycle
import Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch

/-! Connect the unit increment macro to the terminal-marker selector.
The input tape layout is explicit; this is not an all-run invariant. -/
namespace Shared.Beeping.NPcoNP.NativeUnitTerminalBridge
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.NativeUnit261Return1
open Shared.Beeping.NPcoNP.NativeUnit261Cycle83
open Shared.Beeping.NPcoNP.NativeTerminalUnitCycle
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

/-- With the terminal selector window and a run of at least two ones,
the 261 increment returns to state 83 twice. The second return passes
state 10 with a proved marker and retains the incremented bank. -/
theorem dispatch_through_terminal (r v z : Nat) (rest : List Nat)
    (h a : Int) (t : Int → Bool)
    (hr : 1<r) (hpre : t (h-1)=false) (hone : t h=true) (hzero : t (h+1)=false)
    (scanword : Holds t (h+2) (List.replicate r true ++ [false]))
    (bank : Holds t (h+2+(r : Int)+1) (encode (v::rest) ++ [false]))
    (hl : (List.replicate z 0 ++ [1]).length=14)
    (hpos : a+((2*z : Nat):Int)+3=h-1)
    (window : Holds t a (markerWindow (List.replicate z 0 ++ [1])))
    (left : t (a-1)=true) :
    let base := h+2+(r : Int)+1
    let values := (v+1)::rest
    ∃ (mid : Config 284) (n : Nat), mid.state=23 ∧
      silentSegment machine (cfg 261 h t) mid (r+v+6+(encode rest).length) ∧ 0<n ∧
      let u := put (put mid.tape (h-1) true) (h+2) false
      let out := put (clearRange u (h+3) (h+2+(r : Int))) (h+1+(r : Int)) true
      let final := fillRange (setAt h out) (h+2) (h+1+(r : Int))
      Holds final base (encode values) ∧
      (∀ q, base≤q → final q=mid.tape q) ∧
      silentSegment machine mid (cfg 83 (h+(r : Int)-1) final)
        ((encode values).length+r+2+n+(4*z+(r-1)+12)) := by
  dsimp only
  obtain ⟨mid,hstate,hfirst,hbank,hframe,hseg⟩ :=
    Shared.Beeping.NPcoNP.NativeUnitTerminalBridgeExact.dispatch_through_terminal_exact
      r v z rest h a t hr hpre hone hzero scanword bank hl hpos window left
  exact ⟨mid,2*r+7,hstate,hfirst,by omega,hbank,hframe,hseg⟩

#print axioms dispatch_through_terminal
end Shared.Beeping.NPcoNP.NativeUnitTerminalBridge
