import Shared.Beeping.NPcoNP.Grammar284RootStep
import Shared.Beeping.NPcoNP.Grammar284BeepWindow
import Shared.Beeping.NPcoNP.NativeHalfState93Progress

/-! The root's distinct parser code normalizes silently to the ordinary beep
code; the following physical segment matches the graph's single beep. -/
namespace Shared.Beeping.NPcoNP.Grammar284RootBeep
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState93Progress
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284BeepPrepared
open Shared.Beeping.NPcoNP.Grammar284BeepWindow
open Shared.Beeping.NPcoNP.Grammar284ReservedWindow
open Shared.Beeping.NPcoNP.Grammar284RootReady
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem normalize_window (graph : Bank 12) (origin separator : Int) (t : Int → Bool)
    (ready : RootReady graph origin separator t) :
    ReservedWindow 0 graph origin separator (put t (origin+2) false) := by
  obtain ⟨more,room,word,left,gap,right,sep,bank,tail⟩ := ready
  let u := put t (origin+2) false
  have hu : ∀ q, q≠origin+2 → u q=t q := by
    intro q hq
    simp [u,put,hq]
  have h0 : t origin=true := by simpa [rootReadyPath,Holds] using word.1
  have h1 : t (origin+1)=true := by
    simp only [rootReadyPath,Holds] at word
    exact word.2.1
  have h3 : t (origin+3)=false := gap _ (by omega) (by omega)
  have hword : Holds u origin beepPath := by
    simp [beepPath,Holds,u,put,h0,h1,h3,show origin≠origin+2 by omega,
      show origin+1≠origin+2 by omega,show origin+1+1=origin+2 by omega,
      show origin+1+1+1=origin+3 by omega,show origin+2+1=origin+3 by omega,show origin+3≠origin+2 by omega]
  change ReservedWindow 0 graph origin separator u
  refine ⟨beepPath,"beep",more,beep_leaf,room,hword,?_,?_,?_,?_,?_,?_⟩
  · intro q hq
    rw [hu q (by omega)]
    exact left q hq
  · intro q hq hq'
    rw [hu q (by simp [beepPath] at hq; omega)]
    apply gap q <;> simp [beepPath] at hq <;> omega
  · rw [hu _ (by omega)]; exact right
  · rw [hu _ (by omega)]; exact sep
  · apply holds_transport t u (separator+1) _ bank
    intro q hq _
    exact (hu q (by omega)).symm
  · intro q hq
    rw [hu q (by omega)]
    exact tail q hq

/-- Two silent parser steps clear the root boundary's third bit. -/
theorem normalize_segment (origin : Int) (t : Int → Bool) (h1 : t (origin+1)=true) :
    silentSegment machine (cfg 93 (origin+1) t)
      (cfg 259 (origin+3) (put t (origin+2) false)) 2 := by
  have hs := segAdd machine _ _ _ 1 1
    (oneSeg machine _ _ (step93_one (origin+1) t h1))
    (oneSeg machine _ _ (step94 (origin+1+1) t))
  simpa only [show origin+1+1=origin+2 by omega,
    show origin+1+1+1=origin+3 by omega,show origin+2+1=origin+3 by omega] using hs

/-- A root-ready boundary emits exactly the graph beep and reaches row 1. -/
theorem root_beep_step (graph : Bank 12) (origin separator : Int) (t : Int → Bool)
    (ready : RootReady graph origin separator t) :
    ∃ steps out, 0<steps ∧ ReservedWindow 1 graph origin separator out ∧
      physical.advance (cfg 93 (origin+1) t) steps=cfg 93 (origin+1) out ∧
      physical.wordFrom (cfg 93 (origin+1) t) steps=[true] := by
  have h1 : t (origin+1)=true := by
    obtain ⟨_,_,word,_⟩ := ready
    simp only [rootReadyPath,Holds] at word
    exact word.2.1
  let u := put t (origin+2) false
  have hu1 : u (origin+1)=true := by simp [u,put,show origin+1≠origin+2 by omega,h1]
  have hput : put u (origin+2) false=u := by
    funext q
    simp [u,put]
  have hs1 := normalize_segment origin t h1
  have hs2 : silentSegment machine (cfg 93 (origin+1) u)
      (cfg 259 (origin+3) u) 2 := by
    simpa only [hput] using normalize_segment origin u hu1
  obtain ⟨htadv,htword⟩ := silent_physical _ _ _ hs1
  obtain ⟨huadv,huword⟩ := silent_physical _ _ _ hs2
  obtain ⟨n,out,hn,hwindow,hadvance,hevent⟩ := beep_step graph origin separator u (normalize_window graph origin separator t ready)
  have hn2 : 2≤n := by
    by_contra hnot
    have hn1 : n=1 := by omega
    subst n
    obtain ⟨_,hquiet⟩ := silent_physical _ _ 1 (oneSeg machine _ _ (step93_one (origin+1) u hu1))
    rw [hquiet] at hevent
    contradiction
  have hnform : n=2+(n-2) := by omega
  have ha : physical.advance (cfg 93 (origin+1) t) n = physical.advance (cfg 93 (origin+1) u) n := by
    rw [hnform,WordEventSystem.advance_add,WordEventSystem.advance_add,htadv,huadv]
  have hw : physical.wordFrom (cfg 93 (origin+1) t) n = physical.wordFrom (cfg 93 (origin+1) u) n := by
    rw [hnform,WordEventSystem.wordFrom_add,WordEventSystem.wordFrom_add,htadv,huadv,htword,huword]
  exact ⟨n,out,hn,hwindow,ha.trans hadvance,hw.trans hevent⟩

#print axioms normalize_window
#print axioms root_beep_step
end Shared.Beeping.NPcoNP.Grammar284RootBeep
