import Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalExact
import Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalLayout
import Shared.Beeping.NPcoNP.NativeUnitControlMerge
import Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser

/-! A complete, non-existential tape and selector layout at an exact
blank-start boundary. This does not identify the executing graph PC. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284TerminalFullExact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeUnitControlMerge
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
open Shared.Beeping.NPcoNP.Bootstrap284AllZeroReturn
open Shared.Beeping.NPcoNP.Bootstrap284TerminalExact
open Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalNet
open Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalExact
open Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalLayout
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- The exact net output is the previous tape with these five explicit cell
updates. Cells not listed retain their previous values. -/
def terminalTape (p : Int) : Bool :=
  if p= -5 ∨ p=5 ∨ p=6 ∨ p=8 then true else
    if p=7 then false else afterAllZero p

/-- The bank word and whole-tape frame uniquely determine the former
existential output tape. -/
theorem terminal_out_eq (mid : Config 284)
    (hb : Holds (terminalOut mid) 5 (encode [1,0]))
    (hf : ∀ q, q≠ -5 → (q<5 ∨ 8<q) → terminalOut mid q=afterAllZero q) :
    terminalOut mid=terminalTape := by
  have hbits : terminalOut mid 5=true ∧ terminalOut mid 6=true ∧
      terminalOut mid 7=false ∧ terminalOut mid 8=true := by
    have h := hb
    simp [Holds,encode,block] at h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩
  have hleft : terminalOut mid (-5)=true := by simp [terminalOut,setAt]
  funext p
  by_cases hm : p= -5
  · subst p; simpa [terminalTape] using hleft
  by_cases h5 : p=5
  · subst p; simpa [terminalTape] using hbits.1
  by_cases h6 : p=6
  · subst p; simpa [terminalTape] using hbits.2.1
  by_cases h7 : p=7
  · subst p; simpa [terminalTape] using hbits.2.2.1
  by_cases h8 : p=8
  · subst p; simpa [terminalTape] using hbits.2.2.2
  have he : terminalOut mid p=afterAllZero p := hf p hm (by omega)
  simpa [terminalTape,hm,h5,h6,h7,h8] using he

/-- Recover the next complete 14-block selector window from the exact output
and the previous checked layout. -/
theorem exact_next_window :
    Holds terminalTape (-32) (markerWindow (List.replicate 12 0 ++ [3,3])) ∧
    terminalTape (-33)=true ∧ terminalTape 2=true := by
  have hw : Holds afterAllZero (-30) (markerWindow (List.replicate 11 0 ++ 1::0::3::[])) := by
    simpa using afterAllZero_window.1
  have hleft0 : afterAllZero ((-30 : Int)-2)=false := by simpa using after_control_left.1
  have hleft1 : afterAllZero ((-30 : Int)-1)=true := by simpa using after_control_left.2.1
  have hbefore : afterAllZero ((-30 : Int)-3)=true := by simpa using after_control_left.2.2
  have hright : afterAllZero ((-30 : Int)+
      ((encode (List.replicate 11 0 ++ 1::0::3::[])).length : Int))=true := by
    simpa [encode,block,List.replicate_succ] using afterAllZero_window.2.2
  have hwrite : terminalTape ((-30 : Int)+((2*11+3 : Nat):Int))=true := by
    simp [terminalTape]
  have hframe : ∀ q, q≤(-30 : Int)+
      ((encode (List.replicate 11 0 ++ 1::0::3::[])).length : Int) →
      q≠(-30 : Int)+((2*11+3 : Nat):Int) → terminalTape q=afterAllZero q := by
    intro q hq hn
    have hq' : q≤2 := by simpa [encode,block,List.replicate_succ] using hq
    have hn' : q≠ -5 := by simpa using hn
    simp [terminalTape,hn',show q≠(5 : Int) by omega,show q≠(6 : Int) by omega,
      show q≠(7 : Int) by omega,show q≠(8 : Int) by omega]
  have h := merge_control_window afterAllZero terminalTape (-30) 11 3 []
    hw hleft0 hleft1 hbefore hright hwrite hframe
  simpa [encode,block,List.replicate_succ] using h

/-- Exact complete physical tape, marked selector and two-cell bank at the
checked blank-start time. All previous transitions are silent. -/
theorem blank_start_exact_layout :
    machine.system.run 2134099=cfg 83 1 terminalTape ∧
    Holds terminalTape (-32) (markerWindow (List.replicate 12 0 ++ [3,3])) ∧
    terminalTape (-33)=true ∧ terminalTape 2=true ∧
    Holds terminalTape 5 (encode [1,0]) ∧
    silentSegment machine (machine.system.run 0) (cfg 83 1 terminalTape) 2134099 := by
  obtain ⟨mid,_,hb,hf,hseg⟩ := checked_unit_terminal_net_exact
  have heq := terminal_out_eq mid hb hf
  rw [heq] at hb hseg
  have hblank := segAdd machine _ _ _ 2133925 174 blank_start_all_zero_return_exact hseg
  have hrun : machine.system.run 2134099=cfg 83 1 terminalTape := by
    apply run_of_initial_segment
    exact hblank
  exact ⟨hrun,exact_next_window.1,exact_next_window.2.1,exact_next_window.2.2,hb,hblank⟩

/-- The exact new marked window pays the next selector scan: after 35
silent transitions the blank-start run reaches state 93 at head -32, with
the entire reconstructed tape unchanged. -/
theorem blank_start_next_dispatch_exact :
    machine.system.run 2134134=cfg 93 (-32) terminalTape ∧
    silentSegment machine (machine.system.run 0) (cfg 93 (-32) terminalTape) 2134134 := by
  have hsel := marker_window_to93 terminalTape (-32) (List.replicate 12 0 ++ [3,3])
    (by decide) exact_next_window.1 exact_next_window.2.1
  have hs : silentSegment machine (cfg 83 1 terminalTape) (cfg 93 (-32) terminalTape) 35 := by
    simpa [encode,block,List.replicate_succ] using hsel
  have hall := segAdd machine _ _ _ 2134099 35 blank_start_exact_layout.2.2.2.2.2 hs
  have hr : machine.system.run 2134134=cfg 93 (-32) terminalTape := by
    apply run_of_initial_segment
    exact hall
  exact ⟨hr,hall⟩

#print axioms blank_start_next_dispatch_exact

/-- The next actual state-83 visit begins with three ones in descending
orientation. This is a fact about tape data, not the source graph PC. -/
theorem terminal_three_ones : terminalTape 1=true ∧ terminalTape 0=true ∧ terminalTape (-1)=true := by
  let xs := markerWindow (List.replicate 12 0 ++ [3,3])
  have hx : Holds terminalTape (-32) xs := exact_next_window.1
  have h31 := holds_get terminalTape (-32) xs hx 31 (by decide)
  have h32 := holds_get terminalTape (-32) xs hx 32 (by decide)
  have h33 := holds_get terminalTape (-32) xs hx 33 (by decide)
  have hb31 : xs[31]=true := by decide
  have hb32 : xs[32]=true := by decide
  have hb33 : xs[33]=true := by decide
  rw [hb31] at h31
  rw [hb32] at h32
  rw [hb33] at h33
  exact ⟨by simpa using h33,by simpa using h32,by simpa using h31⟩

/-- The fixed root-prefixed leaf parser rejects this real state-83 tape. -/
theorem terminal_parser_none : parsePreparedTape 52 terminalTape 1=none := by
  have h : terminalTape (-1)=true := terminal_three_ones.2.2
  simp [parsePreparedTape,h]

/-- No prepared root-to-leaf path occurs at this particular actual selector
head. A global relation must account for other control phases. -/
theorem actual_selector_rejects_prepared_leaf (path : List Bool) (name : String) :
    ¬ (PreparedWalk path (.op name) ∧
      downHolds (machine.system.run 2134099).tape
        (machine.system.run 2134099).head path) := by
  rintro ⟨hw,ht⟩
  rw [blank_start_exact_layout.1] at ht
  change downHolds terminalTape 1 path at ht
  have hp := (parsePreparedTape_iff terminalTape 1 name path.length).2 ⟨path,hw,rfl,ht⟩
  rw [terminal_parser_none] at hp
  contradiction

#print axioms terminal_out_eq
#print axioms exact_next_window
#print axioms blank_start_exact_layout
#print axioms terminal_parser_none
#print axioms actual_selector_rejects_prepared_leaf
end Shared.Beeping.NPcoNP.Bootstrap284TerminalFullExact
