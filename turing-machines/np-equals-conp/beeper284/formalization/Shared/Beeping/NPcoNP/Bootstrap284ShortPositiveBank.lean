import Shared.Beeping.NPcoNP.Bootstrap284ShortPositiveReturn
import Shared.Beeping.NPcoNP.NativePositiveSelectorDirect
import Shared.Beeping.NPcoNP.NativePositiveBankPadding
import Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral

/-! The actual shortened positive selector decrements its bank and returns. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284ShortPositiveBank
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeManyTerminalWindow
open Shared.Beeping.NPcoNP.NativePositiveSelectorDirect
open Shared.Beeping.NPcoNP.NativePositiveBankPadding
open Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
open Shared.Beeping.NPcoNP.Bootstrap284ShortPositiveReturn
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- The next actual positive selector returns to state 83 after a positive
finite silent segment, restoring zero in the first bank value and retaining
96 supplied blank padding cells. -/
theorem blank_start_short_positive_bank_return_with_prefix :
    ∃ (m n k j l : Nat) (e : Config 284) (out : Int → Bool),
      0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ 0<l ∧ e.state=23 ∧
      let t := put (clearRange (put (put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
      let input := fillRange (setAt (-3796) t) (-3794) 3
      Holds out (-3822) (zeroPairs 11) ∧
      out (-3800)=true ∧ out 4=false ∧ (∀ q, q≤ -3823 → out q=false) ∧
      Holds out 5 ((encode (List.replicate 1898 0) ++ [true,false,false]) ++ List.replicate 96 false) ∧
      (∀ q, -3800<q → q<3 → out q=false) ∧ out 3=true ∧
      (∀ q, q< -3800 → out q=input q) ∧
      silentSegment machine (machine.system.run 0) (cfg 83 (-3801) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603+32+3825+3829+l) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hwindow,h2,h3,h4,hray,hbank,hseg⟩ :=
    blank_start_short_positive_return_with_left_ray
  let t := put (clearRange (put (put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
  let input := fillRange (setAt (-3796) t) (-3794) 3
  have hpreinput : Holds input (-3822) (zeroPairs 11) := by
    have hh := holds_prefix_word input (-3822)
      ((markerWindow (List.replicate 11 0 ++ [3,3795])).take 22)
      ((markerWindow (List.replicate 11 0 ++ [3,3795])).drop 22) (by
        simpa only [List.take_append_drop] using hwindow)
    have he : (markerWindow (List.replicate 11 0 ++ [3,3795])).take 22=zeroPairs 11 := by decide
    simpa only [he] using hh
  have hsplit : markerWindow (List.replicate 11 0 ++ [3,3795]) =
      [false,true] ++ markerWindow (List.replicate 10 0 ++ [3,3795]) := by decide
  rw [hsplit] at hwindow
  have htail := holds_append_tail input (-3822) [false,true]
    (markerWindow (List.replicate 10 0 ++ [3,3795])) hwindow
  have hw : Holds input (-3820) (markerWindow (List.replicate 10 0 ++ [0+3,3795])) := by simpa using htail
  have hlen : (encode (List.replicate 10 0 ++ [0+3,3795])).length=3822 := by simp [encode,block_length]
  have hext : Holds input ((-3820:Int)+((encode (List.replicate 10 0 ++ [0+3,3795])).length : Int))
      (List.replicate 2 true ++ [false]) := by
    rw [hlen]
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds]
    norm_num
    exact ⟨h2,h3,h4⟩
  have hrep : List.replicate 98 false=[false,false] ++ List.replicate 96 false := by decide
  have hbankpad : Holds input 5 ((encode (1::List.replicate 1897 0) ++ [false,false]) ++ List.replicate 96 false) := by
    rw [List.append_assoc,←hrep]
    exact hbank
  have hb : Holds input ((-3820:Int)+((2*10 : Nat):Int)+4+(0:Int)+(3795:Int)+(2:Int)+4)
      (encode ((0+1)::List.replicate 1897 0) ++ [false,false]) := by
    have hh := holds_prefix_word input 5 (encode (1::List.replicate 1897 0) ++ [false,false])
      (List.replicate 96 false) hbankpad
    simpa using hh
  have hc := selector_carry_general input (-3820) 10 3795 (by simpa using hw)
  obtain ⟨l,out,hl,hmark,hblank,hresult,hcorr,hstop,hleft,hright,hbody⟩ :=
    terminal_positive_direct_control input (-3820) 10 3795 2 0 (List.replicate 1897 0)
      hw hext (by simpa using hb) hc
  have hresult0 : Holds out 5 (encode (0::List.replicate 1897 0) ++ [true,false,false]) := by simpa using hresult
  have hframe : ∀ q, 5+2+((List.replicate 0 true ++ (List.replicate 1897 0).flatMap
      (fun z => false :: List.replicate (z+1) true)).length : Int)<q → out q=input q := by
    intro q hq
    apply hright
    norm_num only [Nat.reduceMul,Nat.cast_ofNat,Int.reduceAdd,Int.reduceNeg,add_zero]
    exact hq
  have hbankfull : Holds out 5 ((encode (List.replicate 1898 0) ++ [true,false,false]) ++ List.replicate 96 false) := by
    have hh := positive_bank_padding input out 5 0 (List.replicate 1897 0) (List.replicate 96 false)
      hbankpad hresult0 hframe
    exact hh
  have hpreout : Holds out (-3822) (zeroPairs 11) := by
    apply holds_transport input out _ _ hpreinput
    intro q _ hq
    have hl : (zeroPairs 11).length=22 := by rw [zeroPairs_length]
    rw [hl] at hq
    have hh : out q=input q := by simpa using hleft q (by omega)
    exact hh.symm
  have hray' : ∀ q, q≤ -3823 → out q=false := by
    intro q hq
    have hh : out q=input q := by simpa using hleft q (by omega)
    exact hh.trans (hray q hq)
  have hbody' : silentSegment machine (cfg 93 (-3820) input) (cfg 83 (-3801) out) l := by simpa using hbody
  have hall := segAdd machine _ _ _ _ l hseg hbody'
  exact ⟨m,n,k,j,l,e,out,hm,hn,hk,hj,hl,hs,hpreout,by simpa using hmark,by simpa using hblank,hray',
    hbankfull,by simpa using hcorr,by simpa using hstop,by simpa using hleft,hall⟩

/-- Retain the earlier left-ray positive-bank interface. -/
theorem blank_start_short_positive_bank_return_with_left_ray :
    ∃ (m n k j l : Nat) (e : Config 284) (out : Int → Bool),
      0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ 0<l ∧ e.state=23 ∧
      let t := put (clearRange (put (put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
      let input := fillRange (setAt (-3796) t) (-3794) 3
      out (-3800)=true ∧ out 4=false ∧ (∀ q, q≤ -3823 → out q=false) ∧
      Holds out 5 ((encode (List.replicate 1898 0) ++ [true,false,false]) ++ List.replicate 96 false) ∧
      (∀ q, -3800<q → q<3 → out q=false) ∧ out 3=true ∧
      (∀ q, q< -3800 → out q=input q) ∧
      silentSegment machine (machine.system.run 0) (cfg 83 (-3801) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603+32+3825+3829+l) := by
  obtain ⟨m,n,k,j,l,e,out,hm,hn,hk,hj,hl,hs,_hpre,hmark,hblank,hray,hbank,hcorr,hstop,hframe,hseg⟩ :=
    blank_start_short_positive_bank_return_with_prefix
  exact ⟨m,n,k,j,l,e,out,hm,hn,hk,hj,hl,hs,hmark,hblank,hray,hbank,hcorr,hstop,hframe,hseg⟩

/-- Retain the earlier shortened positive-bank interface. -/
theorem blank_start_short_positive_bank_return :
    ∃ (m n k j l : Nat) (e : Config 284) (out : Int → Bool),
      0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ 0<l ∧ e.state=23 ∧
      let t := put (clearRange (put (put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
      let input := fillRange (setAt (-3796) t) (-3794) 3
      out (-3800)=true ∧ out 4=false ∧
      Holds out 5 ((encode (List.replicate 1898 0) ++ [true,false,false]) ++ List.replicate 96 false) ∧
      (∀ q, -3800<q → q<3 → out q=false) ∧ out 3=true ∧
      (∀ q, q< -3800 → out q=input q) ∧
      silentSegment machine (machine.system.run 0) (cfg 83 (-3801) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603+32+3825+3829+l) := by
  obtain ⟨m,n,k,j,l,e,out,hm,hn,hk,hj,hl,hs,hmark,hblank,_hray,hbank,hcorr,hstop,hframe,hseg⟩ :=
    blank_start_short_positive_bank_return_with_left_ray
  exact ⟨m,n,k,j,l,e,out,hm,hn,hk,hj,hl,hs,hmark,hblank,hbank,hcorr,hstop,hframe,hseg⟩

#print axioms blank_start_short_positive_bank_return
end Shared.Beeping.NPcoNP.Bootstrap284ShortPositiveBank
