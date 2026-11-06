import Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveNext
import Shared.Beeping.NPcoNP.NativeVariablePositiveRedispatch
import Shared.Beeping.NPcoNP.NativeVariableUnitRedispatch

/-! Apply the variable positive bank redispatch at the next reachable stage. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveRedispatch
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeVariablePositiveRedispatch
open Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral

open Shared.Beeping.NPcoNP.NativeVariableUnitRedispatch
open Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveNext
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- The next actual positive operation and 31-step redispatch reach a shorter
zero selector with the blank ray and 94 spare cells retained. -/
theorem blank_start_variable_positive_redispatch :
    ∃ (m n k j l p : Nat) (out : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ 0<l ∧ 0<p ∧
      Holds out (-3820) (markerWindow (List.replicate 8 0 ++ [0])) ∧
      out (-3822)=false ∧ out (-3821)=true ∧ (∀ q, q< -3822 → out q=false) ∧
      out (-3802)=true ∧ out 4=false ∧
      Holds out 5 ((encode (List.replicate 1899 0) ++ [true,false,false]) ++ List.replicate 94 false) ∧
      (∀ q, -3802<q → q<3 → out q=false) ∧ out 3=true ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603+32+3825+3829+l+31+7654+22864+7656+p+31) := by
  obtain ⟨m,n,k,j,l,e,hm,hn,hk,hj,hl,hs,hwindow,h2,h3,h4,hray,hbank,hseg⟩ :=
    blank_start_variable_positive_next
  let t := put (clearRange (put (put e.tape (-3799) true) (-3796) false) (-3795) 4) 3 true
  let input := fillRange (setAt (-3798) t) (-3796) 3
  have hlen : (encode (List.replicate 9 0 ++ [3,3797])).length=3822 := by simp [encode,block_length]
  have hext : Holds input ((-3820:Int)+((encode (List.replicate 9 0 ++ [3,3797])).length : Int))
      [true,true,false] := by
    rw [hlen]
    simp only [Holds]
    norm_num
    exact ⟨h2,h3,h4⟩
  have hrep : List.replicate 96 false=[false,false] ++ List.replicate 94 false := by decide
  have hbankpad : Holds input 5 ((encode (1::List.replicate 1898 0) ++ [false,false]) ++ List.replicate 94 false) := by
    rw [List.append_assoc,←hrep]
    exact hbank
  obtain ⟨p,out,hp,hpairs,hleft0,hleft,hray',hmark,hblank,hresult,hcorr,hstop,hnext⟩ :=
    variable_positive_bank_redispatch input (-3820) 9 3797 0 (List.replicate 1898 0)
      (List.replicate 94 false) (by decide) (by simpa using hwindow)
      (by intro q hq; exact hray q (by simpa using hq)) (by simpa using hext) (by simpa using hbankpad)
  have hwin : Holds out (-3820) (markerWindow (List.replicate 8 0 ++ [0])) := by
    have he : markerWindow (List.replicate 8 0 ++ [0])=zeroPairs 9 := by
      simpa using zero_window_pairs 8
    simpa only [he] using hpairs
  have hnext' : silentSegment machine (cfg 93 (-3820) input) (cfg 93 (-3820) out) (p+31) := by simpa using hnext
  have hall := segAdd machine _ _ _ _ (p+31) hseg hnext'
  refine ⟨m,n,k,j,l,p,out,hm,hn,hk,hj,hl,hp,hwin,by simpa using hleft0,by simpa using hleft,
    by simpa using hray',by simpa using hmark,by simpa using hblank,?_,by simpa using hcorr,by simpa using hstop,?_⟩
  · simpa using hresult
  · simpa [Nat.add_assoc] using hall

#print axioms blank_start_variable_positive_redispatch
end Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveRedispatch
