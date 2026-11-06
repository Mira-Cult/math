import Shared.Beeping.NPcoNP.Bootstrap284FirstBeepBlankRay
import Shared.Beeping.NPcoNP.Grammar284ActiveEndpoint
import Shared.Beeping.NPcoNP.Grammar284BeepPrepared
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
import Shared.Beeping.NPcoNP.Table284LiteralBinding

/-! The real first beep establishes the active graph/tape relation and its
exact event alignment. The physical blank ray was proved through bootstrap. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284AlignedFromBlank
open ComplexityTheory PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284BeepPrepared
open Shared.Beeping.NPcoNP.Grammar284ActiveWindow
open Shared.Beeping.NPcoNP.Grammar284ActiveEndpoint
open Shared.Beeping.NPcoNP.NativeShortStageBlankRay
open Shared.Beeping.NPcoNP.NativeShortCycleStage
open Shared.Beeping.NPcoNP.Bootstrap284FirstBeepBlankRay
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 1024
set_option maxHeartbeats 30000000

def startupValues : List Nat := 0::((List.replicate 1898 0 ++ List.replicate 8 0) ++ [0])
def extraValues : List Nat := startupValues.drop 12

theorem startup_values_prefix : startupValues.take 12=List.replicate 12 0 := by decide

theorem startup_values_split : startupValues=List.replicate 12 0 ++ extraValues := by
  have h := List.take_append_drop 12 startupValues
  simpa only [startup_values_prefix,extraValues] using h.symm

theorem initial_array : arrayBank target.system.initial.bank=List.replicate 12 0 := by decide

theorem aligned_from_blank : AlignedActiveWindow := by
  obtain ⟨time,t,hmarker,hpre,h0,h1,h2,hafter,hmark,hsep,hbank,hleft,hzero,hcontrol,hray,hseg⟩ :=
    blank_start_reaches_first_beep_with_blank_ray
  have hword : Holds t (-3821) beepPath := by
    simp only [beepPath,Holds]
    exact ⟨hpre,h0,h1,h2,trivial⟩
  have hbank0 : Holds t 5 (encode startupValues ++ [true,false]) := by
    apply holds_prefix_word t 5 (encode startupValues ++ [true,false]) ([false] ++ List.replicate 76 false)
    simpa only [startupValues,List.append_assoc,List.cons_append,List.nil_append] using hbank
  have hbank' : Holds t 5 (encode (arrayBank target.system.initial.bank ++ extraValues) ++ [true,false]) := by
    rw [initial_array,←startup_values_split]
    exact hbank0
  have htail : ∀ q, 4+2+((encode (arrayBank target.system.initial.bank++extraValues)).length : Int)≤q → t q=false := by
    intro q hq
    apply hray q
    change 5+((encode startupValues).length : Int)+1≤q
    rw [initial_array,←startup_values_split] at hq
    omega
  obtain ⟨n,out,hn,hwindow,hadvance,hevent⟩ := beep_from_entry target.system.initial.bank extraValues (-3821) 4 t
    (by omega) hword hleft (by simpa using hmarker) (by simpa using hafter) (by simpa using hzero)
    (by intro q hq hq'; exact hcontrol q (by omega) hq') hsep (by simpa using hbank') htail
  obtain ⟨hstart,hquiet⟩ := silent_physical _ _ _ hseg
  have hrun : physical.run time=cfg 99 (-3817) t := by
    change physical.advance machine.initial time=_ at hstart
    change physical.advance machine.initial time=_
    exact hstart
  have hprefix : physical.prefixWord time=[] := by
    change physical.wordFrom machine.initial time=[] at hquiet
    change physical.wordFrom machine.initial time=[]
    exact hquiet
  have hevent' : physical.wordFrom (cfg 99 (-3817) t) n=[true] := by
    simpa only [show (-3821:Int)+4= -3817 by norm_num] using hevent
  have hgraph : target.system.run 1=⟨1,target.system.initial.bank⟩ := by rfl
  have hgraphword : target.system.prefixWord 1=[true] := by rfl
  refine ⟨1,time+n,-3821,4,out,?_,?_,?_⟩
  · rw [WordEventSystem.run_add,hrun]
    simpa using hadvance
  · rw [WordEventSystem.prefix_add,hprefix,hrun,hevent',hgraphword]
    rfl
  · rw [hgraph]
    exact Or.inl hwindow

/-- The selected literal 284-state machine is eventually silent exactly when
NP equals coNP. -/
theorem selected_table_silent_iff_classes : machine.system.EventuallySilent ↔ NP = coNP :=
  selected_table_silent_iff_classes_of_aligned aligned_from_blank

/-- The pinned table text parses to this very machine, and that machine's
finite-beeping condition has the canonical class characterization. -/
theorem literal_table_silent_iff_classes :
    Table284LiteralBinding.parseMachine Table284.SourceChars.source=some machine ∧
      (machine.system.EventuallySilent ↔ NP = coNP) :=
  ⟨Table284LiteralBinding.source_parses_to_machine,selected_table_silent_iff_classes⟩

#print axioms literal_table_silent_iff_classes
#print axioms aligned_from_blank
#print axioms selected_table_silent_iff_classes
end Shared.Beeping.NPcoNP.Bootstrap284AlignedFromBlank
