import Shared.Beeping.NPcoNP.NativeUnitTerminalBridgeExact
import Shared.Beeping.NPcoNP.NativeTerminalControlAlgebra

/-! Simplify the terminal-selector macro to its exact net tape update. -/
namespace Shared.Beeping.NPcoNP.NativeUnitTerminalSummaryExact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeUnit261Return1
open Shared.Beeping.NPcoNP.NativeUnitTerminalBridgeExact
open Shared.Beeping.NPcoNP.NativeTerminalControlAlgebra
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

/-- The compound macro restores the scanned ones, retains the incremented
bank, and changes only the previous left marker outside that bank. -/
theorem dispatch_terminal_net_exact (r v z : Nat) (rest : List Nat)
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
    ∃ mid : Config 284, mid.state=23 ∧
      silentSegment machine (cfg 261 h t) mid (r+v+6+(encode rest).length) ∧
      let final := setAt (h-1) (setAt h mid.tape)
      Holds final base (encode values) ∧
      (∀ q, q≠h-1 → (q<base ∨ last<q) → final q=t q) ∧
      silentSegment machine mid (cfg 83 (h+(r : Int)-1) final)
        ((encode values).length+r+2+(2*r+7)+(4*z+(r-1)+12)) := by
  dsimp only
  let base := h+2+(r : Int)+1
  let values := (v+1)::rest
  obtain ⟨mid,hstate,hfirst,hbank,_hframe,hseg⟩ :=
    dispatch_through_terminal_exact r v z rest h a t hr hpre hone hzero scanword bank hl hpos window left
  obtain ⟨other,_hs,_hb,_hm,hframe',hfirst',_hret⟩ :=
    dispatch_increment_return1 r v rest h t (by omega) hone hzero scanword bank
  have he : mid=other := hfirst.1.symm.trans hfirst'.1
  subst other
  have hscan : Holds mid.tape (h+2) (List.replicate r true ++ [false]) := by
    apply holds_transport t mid.tape _ _ scanword
    intro q hq hq'
    symm
    apply hframe' q (by omega)
    left
    have hlen : (List.replicate r true ++ [false]).length=r+1 := by simp
    rw [hlen] at hq'
    omega
  have heq := restore_control r h mid.tape (by omega) hscan
  dsimp only at heq
  rw [heq] at hbank hseg
  let final := setAt (h-1) (setAt h mid.tape)
  have hframe : ∀ q, q≠h-1 →
      (q<base ∨ base+(((v+1)+(encode rest).length : Nat):Int)<q) → final q=t q := by
    intro q hq hout
    by_cases hh : q=h
    · subst q
      simp [final,setAt,hone]
    · have hv := hframe' q hh hout
      simp [final,setAt,hq,hh,hv]
  exact ⟨mid,hstate,hfirst,hbank,hframe,hseg⟩

#print axioms dispatch_terminal_net_exact
end Shared.Beeping.NPcoNP.NativeUnitTerminalSummaryExact
