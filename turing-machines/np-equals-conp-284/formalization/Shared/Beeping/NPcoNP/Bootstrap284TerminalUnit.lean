import Shared.Beeping.NPcoNP.NativeTerminalUnitCycle
import Shared.Beeping.NPcoNP.Bootstrap284Unit261Actual83

/-! The terminal-marker selector cycle applies to the actual blank-start run.
This is a finite seed and not a proof of recurring graph simulation. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284TerminalUnit
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeTerminalUnitSelector
open Shared.Beeping.NPcoNP.NativeTerminalUnitCycle
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
open Shared.Beeping.NPcoNP.Bootstrap284Unit261Actual83
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

theorem left_window : Holds postCarry (-32)
    (markerWindow (List.replicate 13 0 ++ [1])) := by
  rw [terminal_window]
  unfold postCarry carry4Tape postIncrement returnedTape currentTape
  rw [run_2133586]
  simp only [encode,List.replicate_succ,List.replicate_zero,block,List.cons_append,
    List.nil_append,Holds]
  all_goals decide

theorem left_marker : postCarry (-33)=true := by
  unfold postCarry carry4Tape postIncrement returnedTape currentTape
  rw [run_2133586]
  decide

theorem terminal_marker : postCarry (-3)=true := by simp [postCarry,carry4Tape,put,clearRange]
theorem terminal_h0 : postCarry (-2)=false := by
  simp [postCarry,carry4Tape,put,clearRange,postIncrement_h0]
theorem terminal_h1 : postCarry (-1)=false := by
  simp [postCarry,carry4Tape,put,clearRange,postIncrement_h1]

theorem terminal_zeros : ∀ i : Nat, i<3 → postCarry (0+(i : Int))=false := by
  intro i hi
  have he : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases he with rfl | rfl | rfl <;> simp [postCarry,carry4Tape,put,clearRange]

theorem terminal_right : postCarry 3=true := by simp [postCarry,carry4Tape,put]

def postReturn : Int → Bool := fillRange (setAt (-2) postCarry) 0 3

theorem returned_neg2 : returnedTape (-2)=true := by
  simp [returnedTape,fillRange,setAt]

theorem returned_0 : returnedTape 0=true := by simp [returnedTape,fillRange]
theorem returned_1 : returnedTape 1=true := by simp [returnedTape,fillRange]
theorem returned_2 : returnedTape 2=true := by simp [returnedTape,fillRange]
theorem returned_3 : returnedTape 3=true := by
  have h : currentTape 3=true := one_3
  simpa [returnedTape,fillRange,setAt] using h

set_option linter.unusedSimpArgs false in
/-- The full terminal-cycle output is the prior returned tape with two
additional ones. This is an exact two-sided tape equality. -/
theorem postReturn_eq : postReturn = setAt (-3) (setAt 6 returnedTape) := by
  funext p
  by_cases h3 : p= -3
  · subst p; simp [postReturn,postCarry,carry4Tape,postIncrement,fillRange,put,setAt,clearAt,clearRange]
  · by_cases h2 : p= -2
    · subst p; simp [postReturn,postCarry,carry4Tape,postIncrement,fillRange,put,setAt,clearAt,clearRange,returned_neg2]
    · by_cases h0 : p=0
      · subst p; simp [postReturn,postCarry,carry4Tape,postIncrement,fillRange,put,setAt,clearAt,clearRange,returned_0]
      · by_cases h1 : p=1
        · subst p; simp [postReturn,postCarry,carry4Tape,postIncrement,fillRange,put,setAt,clearAt,clearRange,returned_1]
        · by_cases htwo : p=2
          · subst p; simp [postReturn,postCarry,carry4Tape,postIncrement,fillRange,put,setAt,clearAt,clearRange,returned_2]
          · by_cases hthree : p=3
            · subst p; simp [postReturn,postCarry,carry4Tape,postIncrement,fillRange,put,setAt,clearAt,clearRange,returned_3]
            · by_cases hsix : p=6
              · subst p; simp [postReturn,postCarry,carry4Tape,postIncrement,fillRange,put,setAt,clearAt,clearRange]
              · have hn0 : ¬ (0≤p ∧ p<3) := by omega
                have hn1 : ¬ (1≤p ∧ p<4) := by omega
                simp [postReturn,postCarry,carry4Tape,postIncrement,fillRange,put,setAt,clearAt,clearRange,
                  h3,h2,h0,h1,htwo,hthree,hsix,hn0,hn1]

#print axioms postReturn_eq

/-- The checked state-83 output completes the entire terminal selector and
returns to state 83 at head one after exactly 67 silent transitions. -/
theorem checked_terminal_cycle :
    silentSegment machine (cfg 83 (-4) postCarry) (cfg 83 1 postReturn) 67 := by
  have h := terminal_unit_cycle postCarry (-32) 13 3 (by decide) (by decide)
    left_window left_marker terminal_marker terminal_h0 terminal_h1 terminal_zeros terminal_right
  simpa only [postReturn,Nat.cast_ofNat,Int.reduceAdd,Int.reduceSub,Int.reduceNeg,Nat.reduceAdd,Nat.reduceMul] using h

/-- From blank tape, the machine reaches that exact next state-83 tape
after a positive finite prefix and 67 additional silent transitions. -/
theorem blank_start_terminal_return : ∃ n : Nat, 0<n ∧
    silentSegment machine (machine.system.run 0) (cfg 83 1 postReturn) (2133669+n+67) := by
  obtain ⟨n,hn,hseg⟩ := blank_start_unit_to83
  exact ⟨n,hn,segAdd machine _ _ _ (2133669+n) 67 hseg checked_terminal_cycle⟩

/-- The exact two-write description is also a theorem about the actual
blank-start run, with its first return duration kept existential. -/
theorem blank_start_terminal_return_net : ∃ n : Nat, 0<n ∧
    silentSegment machine (machine.system.run 0)
      (cfg 83 1 (setAt (-3) (setAt 6 returnedTape))) (2133669+n+67) := by
  obtain ⟨n,hn,hseg⟩ := blank_start_terminal_return
  rw [postReturn_eq] at hseg
  exact ⟨n,hn,hseg⟩

#print axioms blank_start_terminal_return_net
#print axioms checked_terminal_cycle
#print axioms blank_start_terminal_return
end Shared.Beeping.NPcoNP.Bootstrap284TerminalUnit
