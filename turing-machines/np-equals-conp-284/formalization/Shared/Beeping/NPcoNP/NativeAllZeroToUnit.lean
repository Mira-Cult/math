import Shared.Beeping.NPcoNP.NativeAllZeroToUnitWords

namespace Shared.Beeping.NPcoNP.NativeAllZeroToUnit
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroSelector
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
attribute [local irreducible] machine


/-- The literal table executes the all-zero fill, revisits the rebuilt
selector, and completes its unit dispatch in exactly `2*r+94` silent steps.
The run length is an arbitrary parameter, so this is not a finite trace. -/
theorem fill_to_unit (a : Int) (r : Nat) (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true) :
    silentSegment machine (cfg 93 a t)
      (cfg 12 (a+32) (clearAt (a+30) (filled a r t))) (2*r+94) := by
  have p28 : a+((2*13 : Nat) : Int)+2=a+28 := by norm_num; omega
  have p29 : a+((2*13 : Nat) : Int)+3=a+29 := by norm_num; omega
  have p30 : a+((2*13 : Nat) : Int)+4=a+30 := by norm_num; omega
  have p31 : a+((2*13 : Nat) : Int)+5=a+31 := by norm_num; omega
  have p32 : a+((2*13 : Nat) : Int)+6=a+32 := by norm_num; omega
  have pend : a+((2*13 : Nat) : Int)+6+((r+2 : Nat) : Int)=a+34+(r : Int) := by
    push_cast
    omega
  have hfill := all_zero_fill_return t a 13 (r+2) (by omega) window
    (by rw [p28]; exact marker) (by rw [p29]; exact nextZero)
    (by rw [p30]; exact h0) (by rw [p31]; exact h1)
    (by intro i hi; rw [p32]; exact hz i hi) (by rw [pend]; exact hm)
  have hfill' : silentSegment machine (cfg 93 a t)
      (cfg 83 (a+32+(r : Int)) (filled a r t)) (r+36) := by
    dsimp only at hfill
    rw [p30] at hfill
    have hhead : a+30+((r+2 : Nat) : Int)=a+32+(r : Int) := by push_cast; omega
    have hend : a+30+2+((r+2 : Nat) : Int)=a+34+(r : Int) := by push_cast; omega
    have hstart : a+30+2=a+32 := by omega
    have hcost : 2*13+(r+2)+8=r+36 := by omega
    rw [hhead,hend,hstart,hcost] at hfill
    exact hfill
  have ⟨hword,hleft⟩ := filled_window a r t window marker nextZero h1
  have hlen : (encode (List.replicate 11 0 ++ [1,0,r])).length=r+29 := by
    simp [encode_append,encode,block_length,zeros_length]
    omega
  have hselect := marker_window_to93 (filled a r t) (a+4)
    (List.replicate 11 0 ++ [1,0,r]) (by simp) hword
      (by
        have hp : a+4-1=a+3 := by omega
        rw [hp]
        exact hleft)
  have hselect' : silentSegment machine (cfg 83 (a+32+(r : Int)) (filled a r t))
      (cfg 93 (a+4) (filled a r t)) (r+30) := by
    rw [hlen] at hselect
    have hp : a+4+((r+29 : Nat) : Int)-1=a+32+(r : Int) := by push_cast; omega
    have hc : r+29+1=r+30 := by omega
    rw [hp,hc] at hselect
    exact hselect
  have hunit := marker_unit_to12 (filled a r t) (a+4) 11 0 r [] hword
  have hunit' : silentSegment machine (cfg 93 (a+4) (filled a r t))
      (cfg 12 (a+32) (clearAt (a+30) (filled a r t))) 28 := by
    dsimp only at hunit
    have hd : a+4+((2*11 : Nat) : Int)+4=a+30 := by norm_num; omega
    rw [hd] at hunit
    have hp : a+30+((0 : Nat) : Int)+2=a+32 := by omega
    have hc : 2*11+0+6=28 := by decide
    rw [hp,hc] at hunit
    exact hunit
  have hfirst := segAdd machine _ _ _ (r+36) (r+30) hfill' hselect'
  have hall := segAdd machine _ _ _ ((r+36)+(r+30)) 28 hfirst hunit'
  have he : (r+36)+(r+30)+28=2*r+94 := by omega
  simpa only [he] using hall

#print axioms fill_to_unit
end Shared.Beeping.NPcoNP.NativeAllZeroToUnit
