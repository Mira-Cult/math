import Shared.Beeping.NPcoNP.NativeManyTerminalWindow
import Shared.Beeping.NPcoNP.Bootstrap284ManyShift

/-! The terminal-window variant applies to the checked blank-start seed.
It supplies the formerly hidden continuation run and its stopping zero. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284ManyTerminalActual
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeManyTerminalWindow
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
open Shared.Beeping.NPcoNP.Bootstrap284Unit261Seed
open Shared.Beeping.NPcoNP.Bootstrap284TerminalUnit
open Shared.Beeping.NPcoNP.Bootstrap284ManyShift
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

theorem returned_nine : returnedTape 9=false := by
  unfold returnedTape currentTape
  rw [run_2133586]
  simp [fillRange,setAt,toConfig,cfg,bitSnapshot]

theorem actual_extension : Holds postReturn 2 (List.replicate 2 true ++ [false]) := by
  have h := actual_scanword
  simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds] at h ⊢
  simp_all [postReturn_eq,setAt]

theorem actual_bank_with_blank : Holds postReturn 5 (encode [1] ++ [false,false]) := by
  have h := actual_bank
  have h8 := returned_eight
  have h9 := returned_nine
  simp only [encode,block,List.replicate_succ,List.replicate_zero,List.cons_append,
    List.nil_append,Holds] at h ⊢
  simp_all [postReturn_eq,setAt]

theorem actual_spec_eq : spec (clearAt (-2) postReturn) 7 2 =
    setAt 7 (clearAt 6 (clearAt (-2) postReturn)) := by
  have hb := actual_bank_with_blank
  simp only [encode,block,List.replicate_succ,List.replicate_zero,List.cons_append,
    List.nil_append,Holds,Int.reduceAdd] at hb
  funext p
  by_cases h5 : p=5
  · subst p; simp [spec,clearAt,setAt,hb.1,hb.2.1]
  · by_cases h6 : p=6
    · subst p; simp [spec,clearAt,setAt,hb.2.2.1]
    · by_cases h7 : p=7
      · subst p; simp [spec,clearAt,setAt]
      · have hn : ¬ (7-(2 : Int)≤p ∧ p<7) := by omega
        simp [spec,clearAt,setAt,h5,h6,h7,hn] <;> omega

/-- The generalized terminal selector theorem yields the exact next
blank-start segment and the decoded new zero-valued bank with spare blank. -/
theorem checked_terminal_many :
    let out := setAt 7 (clearAt 6 (clearAt (-2) postReturn))
    Holds out 5 (encode [0,0] ++ [false]) ∧
    silentSegment machine (cfg 83 1 postReturn) (cfg 23 3 out) 76 := by
  dsimp only
  have hw : Holds postReturn (-30) (markerWindow (List.replicate 12 0 ++ [0+3,1])) := by
    simpa [manySelector] using actual_window
  have hext : Holds postReturn (-30+((encode (List.replicate 12 0 ++ [0+3,1])).length : Int))
      (List.replicate 2 true ++ [false]) := by
    simpa [encode_append,encode,block,List.replicate_succ] using actual_extension
  have hb : Holds postReturn (-30+((2*12 : Nat):Int)+4+(0 : Int)+(1 : Int)+(2 : Int)+4)
      (encode ((0+1)::[]) ++ [false,false]) := by simpa using actual_bank_with_blank
  have hm : postReturn ((-30 : Int)-1)=true := by simpa only [Int.reduceSub] using preceding_marker
  have h := terminal_selector_to_bank postReturn (-30) 12 0 1 2 0 []
    (by decide) hm hw hext hb
  have hout : Holds (spec (clearAt (-2) postReturn) 7 2) 5
      (encode [0] ++ [true,false,false]) := by simpa using h.1
  rw [actual_spec_eq] at hout
  have he : encode [0] ++ [true,false,false] = encode [0,0] ++ [false] := by decide
  rw [he] at hout
  refine ⟨hout,?_⟩
  have hseg : silentSegment machine (cfg 83 1 postReturn)
      (cfg 23 3 (spec (clearAt (-2) postReturn) 7 2)) 76 := by
    simpa [encode_append,encode,block,List.replicate_succ] using h.2.2
  rw [actual_spec_eq] at hseg
  exact hseg

/-- Blank-start reachability follows from the earlier terminal-return
certificate; the earlier positive duration remains existential. -/
theorem blank_start_terminal_many : ∃ n : Nat, 0<n ∧
    let out := setAt 7 (clearAt 6 (clearAt (-2) postReturn))
    Holds out 5 (encode [0,0] ++ [false]) ∧
    silentSegment machine (machine.system.run 0) (cfg 23 3 out) (2133669+n+67+76) := by
  obtain ⟨n,hn,hstart⟩ := blank_start_terminal_return
  exact ⟨n,hn,checked_terminal_many.1,
    segAdd machine _ _ _ (2133669+n+67) 76 hstart checked_terminal_many.2⟩

#print axioms blank_start_terminal_many
end Shared.Beeping.NPcoNP.Bootstrap284ManyTerminalActual
