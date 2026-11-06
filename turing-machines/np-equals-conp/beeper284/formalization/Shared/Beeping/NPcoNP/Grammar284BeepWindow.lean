import Shared.Beeping.NPcoNP.Grammar284BeepPrepared
import Shared.Beeping.NPcoNP.NativeTerminalMarkerReturn
import Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch

/-! The graph beep row is simulated from a supplied reserved parser window.
The physical segment emits exactly one true event and preserves the window. -/
namespace Shared.Beeping.NPcoNP.Grammar284BeepWindow
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeTerminalMarkerReturn
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284BeepPrepared
open Shared.Beeping.NPcoNP.Grammar284ReservedWindow
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem beep_leaf : graphLeaf (0 : Fin 185)=some (beepPath,"beep") := by decide

/-- A supplied row-0 reserved parser window matches the graph beep and its
row-1 successor, preserving the reserve and the entire blank tail. -/
theorem beep_step (graph : Bank 12) (origin separator : Int) (t : Int → Bool)
    (window : ReservedWindow 0 graph origin separator t) :
    ∃ steps out, 0<steps ∧ ReservedWindow 1 graph origin separator out ∧
      physical.advance (cfg 93 (origin+1) t) steps=cfg 93 (origin+1) out ∧
      physical.wordFrom (cfg 93 (origin+1) t) steps=[true] := by
  obtain ⟨path,name,more,hleaf,room,word,left,gap,right,sep,bank,tail⟩ := window
  have he : (path,name)=(beepPath,"beep") := Option.some.inj (hleaf.symm.trans beep_leaf)
  cases Prod.mk.inj he with
  | intro hp hn =>
    subst path
    subst name
    have h0 : t origin=true := by simpa [beepPath,Holds] using word.1
    have h1 : t (origin+1)=true := by
      simp only [beepPath,Holds] at word
      exact word.2.1
    have h2 : t (origin+2)=false := by
      simp only [beepPath,Holds] at word
      simpa only [show origin+1+1=origin+2 by omega] using word.2.2.1
    have h3 : t (origin+3)=false := by
      simp only [beepPath,Holds] at word
      simpa only [show origin+1+1+1=origin+3 by omega] using word.2.2.2.1
    let a := origin+1
    let r := (separator-a-7).toNat
    have hr : (r : Int)=separator-a-7 := Int.toNat_of_nonneg (by dsimp [a]; omega)
    have hr2 : 2≤r := by dsimp [a] at *; omega
    have hstop : a+6+(r : Int)=separator-1 := by omega
    have hzeros : ∀ q, a<q → q<a+6+(r : Int) → t q=false := by
      intro q hq hq'
      have he : q=origin+2 ∨ q=origin+3 ∨ origin+4≤q := by dsimp [a] at hq; omega
      rcases he with rfl | rfl | he
      · exact h2
      · exact h3
      · apply gap q <;> simp [beepPath] at * <;> omega
    let mid := fillRange (setAt (a+3) t) (a+6) (a+6+(r : Int))
    have hround := terminal_marker_roundtrip t a r hr2 (by intro q hq; exact left q (by dsimp [a] at hq; omega))
      (by exact left _ (by dsimp [a]; omega)) (by simpa [a] using h0) (by simpa [a] using h1)
      hzeros (by rw [hstop]; exact right)
    have hround' : silentSegment machine (cfg 93 a t) (cfg 93 a mid) (2*r+36) ∧
        mid a=true ∧ mid (a+1)=false ∧ mid (a+2)=false ∧ mid (a+3)=true := by simpa [mid] using hround
    obtain ⟨hseg,_,_,_,hmark⟩ := hround'
    have hframe : ∀ q, q≠a+3 → (q<a+6 ∨ a+6+(r : Int)≤q) → mid q=t q := by
      intro q hne hrange
      simp [mid,fillRange,setAt,hne,show ¬(a+6≤q ∧ q<a+6+(r : Int)) by omega]
    have hpath : Holds mid origin beepPath := by
      apply holds_transport t mid origin beepPath word
      intro q hq hq'
      have hq'' : q<origin+4 := by simpa [beepPath] using hq'
      exact (hframe q (by dsimp [a]; omega) (Or.inl (by dsimp [a]; omega))).symm
    have hleft : ∀ q, q<origin → mid q=false := by
      intro q hq
      rw [hframe q (by dsimp [a]; omega) (Or.inl (by dsimp [a]; omega))]
      exact left q hq
    have hz1 : mid (origin+5)=false := by
      rw [hframe _ (by dsimp [a]; omega) (Or.inl (by dsimp [a]; omega))]
      exact hzeros _ (by dsimp [a]; omega) (by rw [hstop]; omega)
    have hz2 : mid (origin+6)=false := by
      rw [hframe _ (by dsimp [a]; omega) (Or.inl (by dsimp [a]; omega))]
      exact hzeros _ (by dsimp [a]; omega) (by rw [hstop]; omega)
    have hcontrol : ∀ q, origin+7≤q → q<separator → mid q=true := by
      intro q hq hq'
      by_cases hlast : q=separator-1
      · subst q
        rw [hframe _ (by dsimp [a]; omega) (Or.inr (by rw [hstop]))]
        exact right
      · have hh : a+6≤q ∧ q<a+6+(r : Int) := by rw [hstop]; dsimp [a]; omega
        simp [mid,fillRange,hh]
    have hsep : mid separator=false := by
      rw [hframe _ (by dsimp [a]; omega) (Or.inr (by rw [hstop]; omega))]
      exact sep
    have hbank : Holds mid (separator+1) (encode (arrayBank graph++more) ++ [true,false]) := by
      apply holds_transport t mid (separator+1) _ bank
      intro q hq _
      exact (hframe q (by dsimp [a]; omega) (Or.inr (by rw [hstop]; omega))).symm
    have htail : ∀ q, separator+2+((encode (arrayBank graph++more)).length : Int)≤q → mid q=false := by
      intro q hq
      rw [hframe q (by dsimp [a]; omega) (Or.inr (by rw [hstop]; omega))]
      exact tail q hq
    have member := graph_leaf_member (0 : Fin 185) beepPath "beep" beep_leaf
    have walk : PreparedWalk beepPath (.op "beep") := expanded_leaf_follows traceState557.acc producerExpand (beepPath,"beep") member
    obtain ⟨_,hpathTail⟩ := prepared_head_tail mid origin beepPath "beep" walk hpath
    have hentry : operationEntry "beep"=some 99 := by decide
    have hdispatch := expanded_leaf_dispatch_to_entry traceState557.acc producerExpand (beepPath,"beep") member 99 hentry (origin+1) mid hpathTail
    have hdispatch' : silentSegment machine (cfg 93 a mid) (cfg 99 (origin+4) mid) 3 := by
      simpa [a,beepPath,show origin+1+3=origin+4 by omega] using hdispatch
    have hstart := segAdd machine _ _ _ (2*r+36) 3 hseg hdispatch'
    obtain ⟨b,out,hb,hwindow,hadvance,hevent⟩ := beep_from_entry graph more origin separator mid room hpath hleft
      (by simpa [a,show origin+1+3=origin+4 by omega] using hmark) hz1 hz2 hcontrol hsep hbank htail
    obtain ⟨hpre,hpreword⟩ := silent_physical _ _ _ hstart
    have htotal : physical.advance (cfg 93 (origin+1) t) ((2*r+36+3)+b)=cfg 93 (origin+1) out := by
      rw [WordEventSystem.advance_add]
      simpa [a] using (hpre ▸ hadvance)
    have hword : physical.wordFrom (cfg 93 (origin+1) t) ((2*r+36+3)+b)=[true] := by
      rw [WordEventSystem.wordFrom_add]
      have he : physical.advance (cfg 93 (origin+1) t) (2*r+36+3)=cfg 99 (origin+4) mid := by simpa [a] using hpre
      rw [he,hevent]
      simpa [a] using hpreword
    exact ⟨2*r+36+3+b,out,by omega,hwindow,htotal,hword⟩

#print axioms beep_step
end Shared.Beeping.NPcoNP.Grammar284BeepWindow
