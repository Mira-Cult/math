import Shared.Beeping.NPcoNP.Grammar284ReservedWindow
import Shared.Beeping.NPcoNP.NativeBeepCarry
import Shared.Beeping.NPcoNP.NativeBeepReturn
import Shared.Beeping.NPcoNP.NativeCarryPivot
import Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch

/-! A prepared row-0 beep emits one event and carries to the row-1 parser,
preserving a supplied reserved bank. Preparation is separate. -/
namespace Shared.Beeping.NPcoNP.Grammar284BeepPrepared
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeCarryPivot
open Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284ReservedWindow
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

def beepPath : Path := [true,true,false,false]
def nextPath : Path := [true,true,false,true,false,false]

theorem graph_beep (bank : Bank 12) : target.system.step ⟨0,bank⟩=(⟨1,bank⟩,[true]) := by rfl
theorem next_leaf : graphLeaf (1 : Fin 185)=some (nextPath,"3.$coalesced.4.decnz") := by decide

/-- The literal state-99 event and carry produce the graph's row-1 reserved
window, with exactly one true event in the physical word. -/
theorem beep_from_entry (graph : Bank 12) (more : List Nat) (origin separator : Int) (t : Int → Bool)
    (room : origin+59≤separator) (word : Holds t origin beepPath)
    (left : ∀ q, q<origin → t q=false)
    (marker : t (origin+4)=true) (z1 : t (origin+5)=false) (z2 : t (origin+6)=false)
    (control : ∀ q, origin+7≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode (arrayBank graph++more) ++ [true,false]))
    (tail : ∀ q, separator+2+((encode (arrayBank graph++more)).length : Int)≤q → t q=false) :
    ∃ steps out, 0<steps ∧ ReservedWindow 1 graph origin separator out ∧
      physical.advance (cfg 99 (origin+4) t) steps=cfg 93 (origin+1) out ∧
      physical.wordFrom (cfg 99 (origin+4) t) steps=[true] := by
  let u := put t (origin+4) false
  have hw : Holds u origin beepPath := by
    apply holds_transport t u origin beepPath word
    intro q hq hq'
    simp [u,put,beepPath] at hq'
    simp [u,put,show q≠origin+4 by omega]
  have hl : ∀ q, q<origin → u q=false := by
    intro q hq
    simpa [u,put,show q≠origin+4 by omega] using left q hq
  have hfirst : u origin=true := by
    have hh := hw
    simpa [beepPath,Holds] using hh.1
  have hanchor : u (origin+2)=false := by
    have hh := hw
    simp only [beepPath,Holds] at hh
    simpa only [show origin+1+1=origin+2 by omega] using hh.2.2.1
  have hmark : u (origin+7)=true := by
    simpa [u,put,show origin+7≠origin+4 by omega] using control (origin+7) (by omega) (by omega)
  have hbetween : ∀ q, origin+3<q → q<origin+7 → u q=false := by
    intro q hq hq'
    have he : q=origin+4 ∨ q=origin+5 ∨ q=origin+6 := by omega
    rcases he with rfl | rfl | rfl
    · simp [u,put]
    · simpa [u,put,show origin+5≠origin+4 by omega] using z1
    · simpa [u,put,show origin+6≠origin+4 by omega] using z2
  have hones : ∀ q, origin+7<q → q<separator → u q=true := by
    intro q hq hq'
    simpa [u,put,show q≠origin+4 by omega] using control q (by omega) hq'
  have hsep : u separator=false := by
    simpa [u,put,show separator≠origin+4 by omega] using sep
  obtain ⟨a,out,ha,hout,houtleft,hgap,houtsep,houtmark,hframe,hcarry⟩ :=
    carry_produces_candidate_exact u origin (origin+3) (origin+7) separator beepPath nextPath 0 3 2
      (by decide) (by simp [beepPath]; omega) (by decide) (by decide) (by decide)
      (by intro j hj hj'; simp [beepPath] at hj'; omega)
      (by decide) (by simp [nextPath]; omega) (by decide) hw hfirst hanchor hl (by omega)
      hmark hbetween (by omega) hones hsep
  have hbank : Holds out (separator+1) (encode (arrayBank graph++more) ++ [true,false]) := by
    apply holds_transport t out (separator+1) _ bank
    intro q hq _
    rw [hframe q (by omega)]
    simp [u,put,show q≠origin+4 by omega]
  have htail : ∀ q, separator+2+((encode (arrayBank graph++more)).length : Int)≤q → out q=false := by
    intro q hq
    rw [hframe q (by omega)]
    simpa [u,put,show q≠origin+4 by omega] using tail q hq
  have hwindow : ReservedWindow 1 graph origin separator out :=
    ⟨nextPath,"3.$coalesced.4.decnz",more,next_leaf,room,hout,houtleft,hgap,houtmark,houtsep,hbank,htail⟩
  obtain ⟨hadvance,hevent⟩ := beep_then_silent (origin+4) t marker a (cfg 93 (origin+1) out) (by simpa [u,show origin+4-1=origin+3 by omega] using hcarry)
  exact ⟨1+a,out,by omega,hwindow,hadvance,hevent⟩

#print axioms beep_from_entry
end Shared.Beeping.NPcoNP.Grammar284BeepPrepared
