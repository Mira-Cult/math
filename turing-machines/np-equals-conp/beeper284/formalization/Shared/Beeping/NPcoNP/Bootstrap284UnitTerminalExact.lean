import Shared.Beeping.NPcoNP.NativeUnitWindowTerminalNetExact
import Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalNet
import Shared.Beeping.NPcoNP.Bootstrap284TerminalExact

/-! Exact timing for the checked unit/terminal compound segment. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalExact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeUnitWindowTerminalNetExact
open Shared.Beeping.NPcoNP.Bootstrap284AllZeroReturn
open Shared.Beeping.NPcoNP.Bootstrap284UnitWindow83
open Shared.Beeping.NPcoNP.Bootstrap284UnitNext93
open Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalNet
open Shared.Beeping.NPcoNP.Bootstrap284TerminalExact
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 12000000

/-- Exact 174-step silent compound unit/terminal cycle, with its bank and
whole outside-bank frame. -/
theorem checked_unit_terminal_net_exact : ∃ mid : Config 284, mid.state=23 ∧
    Holds (terminalOut mid) 5 (encode [1,0]) ∧
    (∀ q, q≠ -5 → (q<5 ∨ 8<q) → terminalOut mid q=afterAllZero q) ∧
    silentSegment machine (cfg 83 1 afterAllZero) (cfg 83 1 (terminalOut mid)) 174 := by
  have hw : Holds afterAllZero (-30) (markerWindow (List.replicate 11 0 ++ 1::0::3::[])) := by
    simpa using afterAllZero_window.1
  have hentry := marker_window_to93 afterAllZero (-30) (List.replicate 11 0 ++ [1,0,3])
    (by decide) (by simpa using hw) afterAllZero_window.2.1
  have hentry' : silentSegment machine (cfg 83 1 afterAllZero) (cfg 93 (-30) afterAllZero) 33 := by
    simpa [encode,block,List.replicate_succ] using hentry
  obtain ⟨mid,hs,hbank,hframe,hseg⟩ :=
    unit_through_terminal_net_exact afterAllZero (-30) (-34) 11 3 6 0 [] [0] hw (by decide)
      (by simpa using after_pre) (by simpa using after_scanword) (by simpa using after_bank)
      (by decide) (by decide) after_next_window.1 after_next_window.2
  have hb : Holds (terminalOut mid) 5 (encode [1,0]) := by simpa [terminalOut,encode,block] using hbank
  have hf : ∀ q, q≠ -5 → (q<5 ∨ 8<q) → terminalOut mid q=afterAllZero q := by
    simpa [terminalOut,encode,block] using hframe
  have hc : silentSegment machine (cfg 93 (-30) afterAllZero) (cfg 83 1 (terminalOut mid)) 141 := by
    simpa [terminalOut,encode,block] using hseg
  exact ⟨mid,hs,hb,hf,segAdd machine _ _ _ 33 141 hentry' hc⟩

/-- At exactly 2,134,099 transitions, the blank-start table has completed the
compound cycle silently and has the specified bank and control frame. -/
theorem blank_start_unit_terminal_net_exact : ∃ mid : Config 284, mid.state=23 ∧
    Holds (terminalOut mid) 5 (encode [1,0]) ∧
    (∀ q, q≠ -5 → (q<5 ∨ 8<q) → terminalOut mid q=afterAllZero q) ∧
    silentSegment machine (machine.system.run 0) (cfg 83 1 (terminalOut mid)) 2134099 := by
  obtain ⟨mid,hs,hb,hf,hseg⟩ := checked_unit_terminal_net_exact
  exact ⟨mid,hs,hb,hf,segAdd machine _ _ _ 2133925 174 blank_start_all_zero_return_exact hseg⟩

#print axioms checked_unit_terminal_net_exact
#print axioms blank_start_unit_terminal_net_exact
end Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalExact
