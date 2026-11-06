import Shared.Beeping.NPcoNP.NativeUnitWindowTerminalNet
import Shared.Beeping.NPcoNP.Bootstrap284UnitNext93

/-! The checked unit increment and subsequent terminal selector have an
explicit compound tape effect. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalNet
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeUnitWindowTerminalNet
open Shared.Beeping.NPcoNP.Bootstrap284AllZeroReturn
open Shared.Beeping.NPcoNP.Bootstrap284UnitWindow83
open Shared.Beeping.NPcoNP.Bootstrap284UnitNext93
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 12000000

def terminalOut (mid : Config 284) : Int → Bool := setAt (-5) (setAt (-4) mid.tape)

/-- The seed increments its first bank value, then traverses the recovered
terminal selector and returns to the original state-83 head. The exact net
control and bank frame is specified; the internal duration remains finite
and existential in this theorem. -/
theorem checked_unit_terminal_net : ∃ (mid : Config 284) (n : Nat), mid.state=23 ∧ 0<n ∧
    Holds (terminalOut mid) 5 (encode [1,0]) ∧
    (∀ q, q≠ -5 → (q<5 ∨ 8<q) → terminalOut mid q=afterAllZero q) ∧
    silentSegment machine (cfg 83 1 afterAllZero) (cfg 83 1 (terminalOut mid)) (155+n) := by
  have hw : Holds afterAllZero (-30) (markerWindow (List.replicate 11 0 ++ 1::0::3::[])) := by
    simpa using afterAllZero_window.1
  have hentry := marker_window_to93 afterAllZero (-30) (List.replicate 11 0 ++ [1,0,3])
    (by decide) (by simpa using hw) afterAllZero_window.2.1
  have hentry' : silentSegment machine (cfg 83 1 afterAllZero) (cfg 93 (-30) afterAllZero) 33 := by
    simpa [encode,block,List.replicate_succ] using hentry
  obtain ⟨mid,n,hs,hn,hbank,hframe,hseg⟩ :=
    unit_through_terminal_net afterAllZero (-30) (-34) 11 3 6 0 [] [0] hw (by decide)
      (by simpa using after_pre) (by simpa using after_scanword) (by simpa using after_bank)
      (by decide) (by decide) after_next_window.1 after_next_window.2
  have hb : Holds (terminalOut mid) 5 (encode [1,0]) := by simpa [terminalOut,encode,block] using hbank
  have hf : ∀ q, q≠ -5 → (q<5 ∨ 8<q) → terminalOut mid q=afterAllZero q := by
    simpa [terminalOut,encode,block] using hframe
  have hc : silentSegment machine (cfg 93 (-30) afterAllZero) (cfg 83 1 (terminalOut mid)) (122+n) := by
    have hh : silentSegment machine (cfg 93 (-30) afterAllZero)
        (cfg 83 1 (terminalOut mid)) (40+(13+n+69)) := by
      simpa [terminalOut,encode,block] using hseg
    have he : 40+(13+n+69)=122+n := by omega
    rw [he] at hh
    exact hh
  have hall := segAdd machine _ _ _ 33 (122+n) hentry' hc
  have hcst : 33+(122+n)=155+n := by omega
  rw [hcst] at hall
  exact ⟨mid,n,hs,hn,hb,hf,hall⟩

/-- Blank-start composition of the compound unit/terminal segment. -/
theorem blank_start_unit_terminal_net : ∃ (m n : Nat) (mid : Config 284), 0<m ∧ 0<n ∧
    mid.state=23 ∧ Holds (terminalOut mid) 5 (encode [1,0]) ∧
    (∀ q, q≠ -5 → (q<5 ∨ 8<q) → terminalOut mid q=afterAllZero q) ∧
    silentSegment machine (machine.system.run 0) (cfg 83 1 (terminalOut mid))
      (2133669+m+67+76+10+20+29+39+(155+n)) := by
  obtain ⟨m,hm,hstart⟩ := blank_start_all_zero_return
  obtain ⟨mid,n,hs,hn,hbank,hframe,hseg⟩ := checked_unit_terminal_net
  exact ⟨m,n,mid,hm,hn,hs,hbank,hframe,
    segAdd machine _ _ _ (2133669+m+67+76+10+20+29+39) (155+n) hstart hseg⟩

#print axioms checked_unit_terminal_net
#print axioms blank_start_unit_terminal_net
end Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalNet
