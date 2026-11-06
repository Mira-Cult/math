import Shared.Beeping.NPcoNP.NativeUnitTerminalSummaryExact
import Shared.Beeping.NPcoNP.NativeUnitTerminalBridge
import Shared.Beeping.NPcoNP.NativeTerminalControlAlgebra

/-! Simplify the terminal-selector macro to its exact net tape update. -/
namespace Shared.Beeping.NPcoNP.NativeUnitTerminalSummary
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeUnit261Return1
open Shared.Beeping.NPcoNP.NativeUnitTerminalBridge
open Shared.Beeping.NPcoNP.NativeTerminalControlAlgebra
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

/-- The compound macro restores the scanned ones, retains the incremented
bank, and changes only the previous left marker outside that bank. -/
theorem dispatch_terminal_net (r v z : Nat) (rest : List Nat)
    (h a : Int) (t : Int → Bool)
    (hr : 1<r) (hpre : t (h-1)=false) (hone : t h=true) (hzero : t (h+1)=false)
    (scanword : Holds t (h+2) (List.replicate r true ++ [false]))
    (bank : Holds t (h+2+(r : Int)+1) (encode (v::rest) ++ [false]))
    (hl : (List.replicate z 0 ++ [1]).length=14)
    (hpos : a+((2*z : Nat):Int)+3=h-1)
    (window : Holds t a (markerWindow (List.replicate z 0 ++ [1])))
    (left : t (a-1)=true) :
    let base := h+2+(r : Int)+1
    let last := base+(((v+1)+(encode rest).length : Nat):Int)
    let values := (v+1)::rest
    ∃ (mid : Config 284) (n : Nat), mid.state=23 ∧
      silentSegment machine (cfg 261 h t) mid (r+v+6+(encode rest).length) ∧ 0<n ∧
      let final := setAt (h-1) (setAt h mid.tape)
      Holds final base (encode values) ∧
      (∀ q, q≠h-1 → (q<base ∨ last<q) → final q=t q) ∧
      silentSegment machine mid (cfg 83 (h+(r : Int)-1) final)
        ((encode values).length+r+2+n+(4*z+(r-1)+12)) := by
  dsimp only
  obtain ⟨mid,hstate,hfirst,hbank,hframe,hseg⟩ :=
    Shared.Beeping.NPcoNP.NativeUnitTerminalSummaryExact.dispatch_terminal_net_exact
      r v z rest h a t hr hpre hone hzero scanword bank hl hpos window left
  exact ⟨mid,2*r+7,hstate,hfirst,by omega,hbank,hframe,hseg⟩

#print axioms dispatch_terminal_net
end Shared.Beeping.NPcoNP.NativeUnitTerminalSummary
