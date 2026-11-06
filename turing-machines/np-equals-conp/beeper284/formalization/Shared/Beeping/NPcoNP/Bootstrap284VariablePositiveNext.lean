import Shared.Beeping.NPcoNP.Bootstrap284VariableUnitRedispatch
import Shared.Beeping.NPcoNP.NativeVariablePositiveRoundtrip

/-! The generalized positive round trip on the next actual selector. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveNext
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeVariablePositiveRoundtrip
open Shared.Beeping.NPcoNP.Bootstrap284VariableUnitRedispatch
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- After the generalized unit increment and redispatch, the actual machine
executes the next positive round trip in exactly 7,656 silent transitions. -/
theorem blank_start_variable_positive_next :
    ∃ (m n k j l : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ 0<l ∧ e.state=23 ∧
      let t := put (clearRange (put (put e.tape (-3799) true) (-3796) false) (-3795) 4) 3 true
      let out := fillRange (setAt (-3798) t) (-3796) 3
      Holds out (-3822) (markerWindow (List.replicate 10 0 ++ [3,3797])) ∧
      out 2=true ∧ out 3=true ∧ out 4=false ∧ (∀ q, q< -3822 → out q=false) ∧
      Holds out 5 (encode (1::List.replicate 1898 0) ++ List.replicate 96 false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603+32+3825+3829+l+31+7654+22864+7656) := by
  obtain ⟨m,n,k,j,l,e,hm,hn,hk,hj,hl,hs,hbank,hpre,hleft0,hleft,hray,hmark,hnext,hcorr,hstop,hdelim,hseg⟩ :=
    blank_start_variable_unit_redispatch
  let t := put (clearRange (put (put e.tape (-3799) true) (-3796) false) (-3795) 4) 3 true
  let out := fillRange (setAt (-3798) t) (-3796) 3
  have hz : ∀ i : Nat, i<3797+2 → t ((-3820:Int)+((2*9 : Nat):Int)+6+(i : Int))=false := by
    intro i hi
    apply hcorr <;> norm_num <;> omega
  obtain ⟨hround,hwindow,hframe⟩ := variable_positive_roundtrip t (-3820) 9 3797 (by decide) hpre
    (by intro q hq; exact hray q (by simpa using hq)) (by simpa using hleft0) (by simpa using hleft)
    (by simpa using hmark) (by simpa using hnext) (by apply hcorr <;> norm_num)
    (by apply hcorr <;> norm_num) hz (by simpa using hstop)
  have hround' : silentSegment machine (cfg 93 (-3820) t) (cfg 93 (-3820) out) 7656 := by
    norm_num at hround ⊢
    exact hround
  have hwin : Holds out (-3822) (markerWindow (List.replicate 10 0 ++ [3,3797])) := by simpa using hwindow
  have hf : ∀ q, q< -3798 ∨ 3≤q → out q=t q := by simpa using hframe
  have hray' : ∀ q, q< -3822 → out q=false := by
    intro q hq
    exact (hf q (Or.inl (by omega))).trans (hray q hq)
  have hb : Holds out 5 (encode (1::List.replicate 1898 0) ++ List.replicate 96 false) := by
    apply holds_transport t out _ _ hbank
    intro q hq _
    exact (hf q (Or.inr (by omega))).symm
  have ho2 : out 2=true := by simp [out,fillRange]
  have ho3 : out 3=true := (hf 3 (Or.inr (by norm_num))).trans hstop
  have ho4 : out 4=false := (hf 4 (Or.inr (by norm_num))).trans hdelim
  have hall := segAdd machine _ _ _ _ 7656 hseg hround'
  exact ⟨m,n,k,j,l,e,hm,hn,hk,hj,hl,hs,hwin,ho2,ho3,ho4,hray',hb,hall⟩

#print axioms blank_start_variable_positive_next
end Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveNext
