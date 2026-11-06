import Shared.Beeping.NPcoNP.Bootstrap284AllZeroToUnit
import Shared.Beeping.NPcoNP.NativeAllZeroNextReturn
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
import Shared.Beeping.NPcoNP.NativeAllZeroNearCarry

/-! Extend the actual blank-start prefix through the next bank increment and
its backward scan. This is a finite prefix, not a graph simulation. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284SecondIncrementReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroNextReturn
open Shared.Beeping.NPcoNP.NativeAllZeroNearCarry
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
open Shared.Beeping.NPcoNP.Bootstrap284AllZeroToUnit
open Shared.Beeping.NPcoNP.Bootstrap284SecondAllZeroExact
open Shared.Beeping.NPcoNP.Bootstrap284NextReturnExact
open Shared.Beeping.NPcoNP.Bootstrap284NextSelectorExact
open Shared.Beeping.NPcoNP.UnaryBank

set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000
attribute [local irreducible] machine

def inputTape : Int → Bool := clearAt (-6) afterZero

theorem input_scan_cells : inputTape (-6)=false ∧ inputTape (-5)=false ∧
    Holds inputTape (-4) (List.replicate 8 true ++ [false]) := by
  have hm5 : returnTape (-5)=false := return_zeros (-5) (by omega) (by omega)
  have h3 : returnTape 3=true := return_one
  have h4 : returnTape 4=false := by
    have h := scan28_cells.2.2.1
    simpa [returnTape,put,clearRange] using h
  have hz6 : inputTape (-6)=false := by simp [inputTape,clearAt]
  have hz5 : inputTape (-5)=false := by simpa [inputTape,clearAt,afterZero,fillRange,setAt] using hm5
  have hw : Holds inputTape (-4) (List.replicate 8 true ++ [false]) := by
    simp [inputTape,clearAt,afterZero,fillRange,setAt,List.replicate_succ,Holds,h3,h4]
  exact ⟨hz6,hz5,hw⟩

/-- The literal blank-start run reaches state 1 at head -7 after exactly
2,134,385 transitions; every transition in this prefix is silent. -/
theorem blank_start_second_increment_return :
    ∃ e : Config 284, e.state=23 ∧ e.head=10 ∧
      Holds e.tape 5 (encode [1,0,0]) ∧
      (∀ q, q<5 ∨ 10<q → e.tape q=inputTape q) ∧
      machine.system.run 2134385=cfg 1 (-7) e.tape ∧
      silentSegment machine (machine.system.run 0) (cfg 1 (-7) e.tape) 2134385 := by
  obtain ⟨hz6,hz5,hword⟩ := input_scan_cells
  have hscan : silentSegment machine (cfg 12 (-4) inputTape) (cfg 14 5 inputTape) 9 := by
    simpa using scan12 8 (-4) inputTape hword
  have hbank : Holds inputTape 5 (encode [0,0,0] ++ [false]) := by
    have h := blank_start_unit_bank
    rw [blank_start_unit_dispatch_exact.1] at h
    simpa [inputTape,cfg,encode,block] using h
  obtain ⟨e,hs,hh,hbankout,hframe,hinc⟩ := encoded_increment 0 [0,0] 5 inputTape hbank
  have hh' : e.head=10 := by simpa [encode,block] using hh
  have hinc' : silentSegment machine (cfg 14 5 inputTape) e 7 := by
    simpa [encode,block] using hinc
  have he6 : e.tape (-6)=false := (hframe _ (by simp [encode,block])).trans hz6
  have he5 : e.tape (-5)=false := (hframe _ (by simp [encode,block])).trans hz5
  have herun : Holds e.tape (-4) (List.replicate 8 true ++ [false]) := by
    apply holds_transport inputTape e.tape _ _ hword
    intro q hq hq'
    exact (hframe q (by simp [encode,block] at hq'; omega)).symm
  have hret := bank_run_to1 1 [0,0] (-6) 8 e.tape (by omega) he6 (by simpa using he5)
    (by simpa using herun) (by simpa using hbankout)
  have hecfg : e=cfg 23 10 e.tape := by
    have hc : e=cfg e.state e.head e.tape := by cases e; rfl
    simpa only [hs,hh'] using hc
  have hret' : silentSegment machine e (cfg 1 (-7) e.tape) 17 := by
    have hret'' : silentSegment machine (cfg 23 10 e.tape) (cfg 1 (-7) e.tape) 17 := by
      simpa [encode,block] using hret
    simpa only [←hecfg] using hret''
  have hpre := segAdd machine _ _ _ 2134352 9 blank_start_unit_dispatch_exact.2 hscan
  have hpre' := segAdd machine _ _ _ (2134352+9) 7 hpre hinc'
  have hall := segAdd machine _ _ _ (2134352+9+7) 17 hpre' hret'
  have hall' : silentSegment machine (machine.system.run 0) (cfg 1 (-7) e.tape) 2134385 := by
    simpa [inputTape] using hall
  exact ⟨e,hs,hh',by simpa using hbankout,hframe,run_of_initial_segment 2134385 _ hall',hall'⟩

/-- The following near carry takes 23 more silent transitions, retaining the
incremented bank and giving the complete tape at the state-83 boundary. -/
theorem blank_start_second_near_carry_with_exterior :
    ∃ e : Config 284, e.state=23 ∧ e.head=10 ∧
      let out := put (clearRange (put (put e.tape (-7) true) (-4) false) (-3) 4) 3 true
      Holds out 5 (encode [1,0,0]) ∧
      out (-7)=true ∧ out (-6)=false ∧ out (-5)=false ∧
      (∀ q, q≤ -8 → out q=returnTape q) ∧
      (∀ q, q<5 ∨ 10<q → e.tape q=inputTape q) ∧
      machine.system.run 2134408=cfg 83 (-8) out ∧
      silentSegment machine (machine.system.run 0) (cfg 83 (-8) out) 2134408 := by
  obtain ⟨e,hs,hh,hbank,hframe,_hrun,hseg⟩ := blank_start_second_increment_return
  obtain ⟨hz6,hz5,hword⟩ := input_scan_cells
  have hz7 : inputTape (-7)=false := by
    have h := return_zeros (-7) (by omega) (by omega)
    simpa [inputTape,clearAt,afterZero,fillRange,setAt] using h
  have he7 : e.tape (-7)=false := (hframe _ (by omega)).trans hz7
  have he6 : e.tape (-6)=false := (hframe _ (by omega)).trans hz6
  have he5 : e.tape (-5)=false := (hframe _ (by omega)).trans hz5
  have herun : Holds e.tape (-4) (List.replicate 8 true ++ [false]) := by
    apply holds_transport inputTape e.tape _ _ hword
    intro q hq hq'
    exact (hframe q (by simp at hq'; omega)).symm
  let out := put (clearRange (put (put e.tape (-7) true) (-4) false) (-3) 4) 3 true
  have hcarry := near_carry_to83 (-34) 3 e.tape (by simpa using he7)
    (by simpa using he6) (by simpa using he5) (by simpa using herun)
  have hcarry' : silentSegment machine (cfg 1 (-7) e.tape) (cfg 83 (-8) out) 23 := by
    simpa [out] using hcarry
  have hbank' : Holds out 5 (encode [1,0,0]) := by
    apply holds_transport e.tape out _ _ hbank
    intro q hq _
    symm
    have hf := near_carry_frame (-34) 3 e.tape q (Or.inr (by omega))
    simpa [out] using hf
  have hleft : ∀ q, q≤ -8 → out q=returnTape q := by
    intro q hq
    have hf := near_carry_frame (-34) 3 e.tape q (Or.inl (by omega))
    have heq : e.tape q=inputTape q := hframe q (by omega)
    calc
      out q=e.tape q := by simpa [out] using hf
      _=inputTape q := heq
      _=returnTape q := by
        simp [inputTape,clearAt,afterZero,fillRange,setAt,
          show q≠(-6:Int) by omega,show ¬((-4:Int)≤q ∧ q<3) by omega]
  have h7 : out (-7)=true := by simp [out,put,clearRange]
  have h6 : out (-6)=false := by simp [out,put,clearRange,he6]
  have h5 : out (-5)=false := by simp [out,put,clearRange,he5]
  have hall := segAdd machine _ _ _ 2134385 23 hseg hcarry'
  have hall' : silentSegment machine (machine.system.run 0) (cfg 83 (-8) out) 2134408 := by
    simpa using hall
  exact ⟨e,hs,hh,hbank',h7,h6,h5,hleft,hframe,run_of_initial_segment 2134408 _ hall',hall'⟩

/-- Retain the earlier near-carry frame interface. -/
theorem blank_start_second_near_carry_with_frame :
    ∃ e : Config 284, e.state=23 ∧ e.head=10 ∧
      let out := put (clearRange (put (put e.tape (-7) true) (-4) false) (-3) 4) 3 true
      Holds out 5 (encode [1,0,0]) ∧
      out (-7)=true ∧ out (-6)=false ∧ out (-5)=false ∧
      (∀ q, q≤ -8 → out q=returnTape q) ∧
      machine.system.run 2134408=cfg 83 (-8) out ∧
      silentSegment machine (machine.system.run 0) (cfg 83 (-8) out) 2134408 := by
  obtain ⟨e,hs,hh,hbank,h7,h6,h5,hleft,_hext,hrun,hseg⟩ := blank_start_second_near_carry_with_exterior
  exact ⟨e,hs,hh,hbank,h7,h6,h5,hleft,hrun,hseg⟩

/-- Retain the existing near-carry interface. -/
theorem blank_start_second_near_carry :
    ∃ e : Config 284, e.state=23 ∧ e.head=10 ∧
      let out := put (clearRange (put (put e.tape (-7) true) (-4) false) (-3) 4) 3 true
      Holds out 5 (encode [1,0,0]) ∧
      machine.system.run 2134408=cfg 83 (-8) out ∧
      silentSegment machine (machine.system.run 0) (cfg 83 (-8) out) 2134408 := by
  obtain ⟨e,hs,hh,hbank,_h7,_h6,_h5,_hleft,hrun,hseg⟩ := blank_start_second_near_carry_with_frame
  exact ⟨e,hs,hh,hbank,hrun,hseg⟩

#print axioms input_scan_cells
#print axioms blank_start_second_increment_return
#print axioms blank_start_second_near_carry
#print axioms blank_start_second_near_carry_with_frame
#print axioms blank_start_second_near_carry_with_exterior
end Shared.Beeping.NPcoNP.Bootstrap284SecondIncrementReturn
