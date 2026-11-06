import Shared.Beeping.NPcoNP.Bootstrap284TerminalFullExact
import Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalMany
import Shared.Beeping.NPcoNP.NativeManyTerminalWindow

/-! Exact next positive-bank macro from the reconstructed blank-start tape.
This finite physical segment does not identify the source graph PC. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284NextBankExact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeManyTerminalWindow
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
open Shared.Beeping.NPcoNP.Bootstrap284AllZeroReturn
open Shared.Beeping.NPcoNP.Bootstrap284UnitWindow83
open Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalLayout
open Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalMany
open Shared.Beeping.NPcoNP.Bootstrap284TerminalFullExact
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000
attribute [local irreducible] terminalTape

/-- The state-83 tape has a finite two-one continuation ending in zero. -/
theorem exact_extension : Holds terminalTape 2 (List.replicate 2 true ++ [false]) := by
  have hword := after_scanword
  have h3 := holds_get afterAllZero (-2) _ hword 5 (by decide)
  have h4 := holds_get afterAllZero (-2) _ hword 6 (by decide)
  have hb3 : (List.replicate 6 true ++ [false])[5]=true := by decide
  have hb4 : (List.replicate 6 true ++ [false])[6]=false := by decide
  rw [hb3] at h3
  rw [hb4] at h4
  have ht3 : terminalTape 3=true := by simpa [terminalTape] using h3
  have ht4 : terminalTape 4=false := by simpa [terminalTape] using h4
  simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds]
  exact ⟨exact_next_window.2.2,ht3,ht4,trivial⟩

/-- The backing bank has the two paid blank separators needed by the shift. -/
theorem exact_bank_with_blanks : Holds terminalTape 5 (encode [1,0] ++ [false,false]) := by
  have hb := blank_start_exact_layout.2.2.2.2.1
  have h10 : terminalTape 10=false := by simpa [terminalTape] using after_extra_blank
  have h11 : terminalTape 11=false := by simpa [terminalTape] using after_third_blank
  have ht : Holds terminalTape (5+((encode [1,0]).length : Int)) [false,false] := by
    simpa [encode,block,Holds] using And.intro h10 h11
  exact holds_append_intro terminalTape 5 (encode [1,0]) [false,false] hb ht

/-- Exact complete tape after decrementing the selected positive bank value. -/
def nextBankTape : Int → Bool := spec (clearAt (-4) terminalTape) 9 4

/-- All selector, continuation, bank, and delimiter premises are now checked
for this actual boundary; its physical macrostep has exactly 84 silent steps. -/
theorem next_bank_segment :
    Holds nextBankTape 5 (encode [0,0] ++ [true,false,false]) ∧
    (∀ p, p≠ -4 → (p<5 ∨ 9<p) → nextBankTape p=terminalTape p) ∧
    silentSegment machine (cfg 83 1 terminalTape) (cfg 23 3 nextBankTape) 84 := by
  have hlen : (List.replicate 12 0 ++ [0+3,3]).length=14 := by decide
  have hwindow : Holds terminalTape (-32) (markerWindow (List.replicate 12 0 ++ [0+3,3])) :=
    exact_next_window.1
  have hext : Holds terminalTape
      ((-32 : Int)+((encode (List.replicate 12 0 ++ [0+3,3])).length : Int))
      (List.replicate 2 true ++ [false]) := by
    change Holds terminalTape 2 (List.replicate 2 true ++ [false])
    exact exact_extension
  have hbank : Holds terminalTape
      ((-32 : Int)+((2*12 : Nat):Int)+4+(0 : Int)+(3 : Int)+(2 : Int)+4)
      (encode ((0+1)::[0]) ++ [false,false]) := by
    change Holds terminalTape 5 (encode [1,0] ++ [false,false])
    exact exact_bank_with_blanks
  have hmarker : terminalTape ((-32 : Int)-1)=true := by
    change terminalTape (-33)=true
    exact exact_next_window.2.1
  have h := terminal_selector_to_bank terminalTape (-32) 12 0 3 2 0 [0]
    hlen hmarker hwindow hext hbank
  change Holds nextBankTape 5 (encode [0,0] ++ [true,false,false]) ∧
    (∀ p, p≠ -4 → (p<5 ∨ 9<p) → nextBankTape p=terminalTape p) ∧
    silentSegment machine (cfg 83 1 terminalTape) (cfg 23 3 nextBankTape) 84 at h
  exact h

/-- The selected table reaches that full-tape state at an exact blank-start
time with no events in the prefix. -/
theorem blank_start_next_bank_exact :
    machine.system.run 2134183=cfg 23 3 nextBankTape ∧
    Holds nextBankTape 5 (encode [0,0] ++ [true,false,false]) ∧
    (∀ p, p≠ -4 → (p<5 ∨ 9<p) → nextBankTape p=terminalTape p) ∧
    silentSegment machine (machine.system.run 0) (cfg 23 3 nextBankTape) 2134183 := by
  have hseg := segAdd machine _ _ _ 2134099 84 blank_start_exact_layout.2.2.2.2.2 next_bank_segment.2.2
  have hrun : machine.system.run 2134183=cfg 23 3 nextBankTape := by
    apply run_of_initial_segment
    exact hseg
  exact ⟨hrun,next_bank_segment.1,next_bank_segment.2.1,hseg⟩

#print axioms exact_extension
#print axioms exact_bank_with_blanks
#print axioms next_bank_segment
#print axioms blank_start_next_bank_exact
end Shared.Beeping.NPcoNP.Bootstrap284NextBankExact
