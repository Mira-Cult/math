import Shared.Beeping.NPcoNP.Bootstrap284ShortZeroReturn
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
import Shared.Beeping.NPcoNP.NativeUnitSelectorBankIncrement
import Shared.Beeping.NPcoNP.NativeVariableUnitCarry

/-! The next shortened unit selector reaches and increments the actual bank. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284VariableUnitCarry
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeUnitSelectorBankIncrement
open Shared.Beeping.NPcoNP.NativeVariableUnitCarry
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284ShortZeroReturn
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- The actual shortened selector completes its increment, bank return and
near carry in 22,822 further silent transitions. -/
theorem blank_start_variable_unit_carry :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ e.state=23 ∧
      let out := Shared.Beeping.NPcoNP.NativeHalfSweep.put
        (Shared.Beeping.NPcoNP.NativeHalfState28Exact.clearRange
          (Shared.Beeping.NPcoNP.NativeHalfSweep.put (Shared.Beeping.NPcoNP.NativeHalfSweep.put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
      Holds out 5 (encode (1::List.replicate 1897 0)) ∧
      (∀ q, q≤ -3823 → out q=false) ∧
      silentSegment machine (machine.system.run 0) (cfg 83 (-3798) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+22822) := by
  obtain ⟨m,n,k,j,t,hm,hn,hk,hj,hwindow,hl3,hl4,hl5,hray,hlmark,hz7,hz5,h2,h3,h4,hbank,hseg⟩ :=
    blank_start_short_zero_return_with_left_ray
  let out := fillRange (setAt (-3796) t) (-3794) 3
  let selected := clearAt (-3796) out
  have hsplit : markerWindow (List.replicate 11 0 ++ [1,0,3795]) =
      [false,true] ++ markerWindow (List.replicate 10 0 ++ [1,0,3795]) := by decide
  rw [hsplit] at hwindow
  have htail := holds_append_tail out (-3822) [false,true]
    (markerWindow (List.replicate 10 0 ++ [1,0,3795])) hwindow
  have hw : Holds out (-3820) (markerWindow (List.replicate 10 0 ++ 1::0::3795::[])) := by simpa using htail
  have hrun0 : Holds selected (-3794) (List.replicate 3797 true) := by
    apply holds_of_get
    intro i hi
    have hi' : i<3797 := by simpa using hi
    have hr : (-3794:Int)≤ -3794+(i : Int) ∧ -3794+(i : Int)<3 := by omega
    have hn : (-3794:Int)+(i : Int)≠ -3796 := by omega
    simp only [List.getElem_replicate]
    simp [selected,clearAt,out,fillRange,hr,hn]
  have hpair : Holds selected 3 [true,false] := by
    simp only [Holds]
    refine ⟨?_,?_,trivial⟩
    · simpa [selected,clearAt] using h3
    · simpa [selected,clearAt] using h4
  have hword : Holds selected (-3794) (List.replicate 3798 true ++ [false]) := by
    have hh := holds_append_intro selected (-3794) (List.replicate 3797 true) [true,false] hrun0 (by simpa using hpair)
    have he : List.replicate 3797 true ++ [true,false]=List.replicate 3798 true ++ [false] := by
      rw [show 3798=3797+1 by decide,List.replicate_succ']
      simp [List.append_assoc]
    simpa only [he] using hh
  have hword0 : Holds out (-3794) (List.replicate 3798 true ++ [false]) := by
    apply holds_transport selected out _ _ hword
    intro q hq _
    simp [selected,clearAt,show q≠ -3796 by omega]
  have hbankword : encode (0::List.replicate 1897 0) ++ [false] =
      encode (List.replicate 1897 0) ++ [true,false,false] := by
    have he : 0::List.replicate 1897 0=List.replicate 1897 0 ++ [0] := by
      rw [←List.replicate_succ']
      rfl
    rw [he,append_zero_block]
    simp [List.append_assoc]
  have hbank' : Holds out 5 (encode (0::List.replicate 1897 0) ++ [false]) := by
    rw [hbankword]
    exact holds_prefix_word out 5 (encode (List.replicate 1897 0) ++ [true,false,false])
      (List.replicate 98 false) hbank
  obtain ⟨e,hs,hebank,hleft,_hright,hnext⟩ :=
    variable_unit_increment_carry out (-3820) 10 3795 3793 0 [] (List.replicate 1897 0)
      hw (by simpa using hz7) (by simpa using hz5) (by simpa using hword0) (by simpa using hbank')
  let result := Shared.Beeping.NPcoNP.NativeHalfSweep.put
    (Shared.Beeping.NPcoNP.NativeHalfState28Exact.clearRange
      (Shared.Beeping.NPcoNP.NativeHalfSweep.put (Shared.Beeping.NPcoNP.NativeHalfSweep.put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
  have hlen0 : (encode (List.replicate 1897 0)).length=3794 := by rw [zeros_length]
  have hlen : (encode (1::List.replicate 1897 0)).length=3797 := by
    simp only [encode,List.length_append,block_length,hlen0]
  have hnext' : silentSegment machine (cfg 93 (-3820) out) (cfg 83 (-3798) result) 22822 := by
    simp only [hlen,hlen0] at hnext
    norm_num at hnext ⊢
    exact hnext
  have hbankresult : Holds result 5 (encode (1::List.replicate 1897 0)) := by simpa using hebank
  have hray' : ∀ q, q≤ -3823 → result q=false := by
    intro q hq
    have hh : result q=out q := by simpa using hleft q (by norm_num; omega)
    exact hh.trans (hray q hq)
  have hall := segAdd machine _ _ _ _ 22822 hseg hnext'
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbankresult,hray',hall⟩

#print axioms blank_start_variable_unit_carry
end Shared.Beeping.NPcoNP.Bootstrap284VariableUnitCarry
