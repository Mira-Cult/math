import Shared.Beeping.NPcoNP.Bootstrap284ShortBankReturn
import Shared.Beeping.NPcoNP.Bootstrap284VariableUnitCarry
import Shared.Beeping.NPcoNP.NativeAllZeroNearCarry

/-! The shortened selector's near carry on the actual blank-start run. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284ShortNearCarry
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeAllZeroNearCarry
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.Bootstrap284ShortBankReturn
open Shared.Beeping.NPcoNP.Bootstrap284VariableUnitCarry
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- The actual near carry returns to state 83 in 7,603 further silent
transitions, with the incremented bank intact. -/
theorem blank_start_short_near_carry_with_left_ray :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ e.state=23 ∧
      let out := put (clearRange (put (put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
      Holds out 5 (encode (1::List.replicate 1897 0) ++ List.replicate 98 false) ∧
      Holds out (-3822) (zeroWord.take 24) ∧
      out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧
      (∀ q, q≤ -3823 → out q=false) ∧
      out (-3798)=true ∧ out (-3797)=true ∧
      (∀ q, -3797<q → q<3 → out q=false) ∧ out 3=true ∧ out 4=false ∧
      silentSegment machine (machine.system.run 0) (cfg 83 (-3798) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbank,hpre,hl3,hl4,hl5,hray,hmark,h7,h6,h5,hrun,hseg⟩ :=
    blank_start_short_bank_return_with_left_ray
  have hcarry := near_carry_to83 (-3824) 3793 e.tape
    (by simpa using h7) (by simpa using h6) (by simpa using h5) (by simpa using hrun)
  let out := put (clearRange (put (put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
  have hcarry' : silentSegment machine (cfg 1 (-3797) e.tape) (cfg 83 (-3798) out) 7603 := by
    norm_num at hcarry ⊢
    exact hcarry
  have hbank' : Holds out 5 (encode (1::List.replicate 1897 0) ++ List.replicate 98 false) := by
    apply holds_transport e.tape out _ _ hbank
    intro q hq _
    symm
    have hh := near_carry_frame (-3824) 3793 e.tape q (Or.inr (by norm_num; omega))
    norm_num at hh
    exact hh
  have hleft : ∀ q, q< -3797 → out q=e.tape q := by
    intro q hq
    have hh := near_carry_frame (-3824) 3793 e.tape q (Or.inl (by norm_num; omega))
    norm_num at hh
    exact hh
  have hpref : Holds out (-3822) (zeroWord.take 24) := by
    apply holds_transport e.tape out _ _ hpre
    intro q _ hq
    have hl : (zeroWord.take 24).length=24 := by decide
    rw [hl] at hq
    exact (hleft q (by omega)).symm
  have hray' : ∀ q, q≤ -3823 → out q=false := by
    intro q hq
    exact (hleft q (by omega)).trans (hray q hq)
  have ho3 : out (-3823)=false := (hleft _ (by norm_num)).trans hl3
  have ho4 : out (-3824)=false := (hleft _ (by norm_num)).trans hl4
  have ho5 : out (-3825)=false := (hleft _ (by norm_num)).trans hl5
  have ho8 : out (-3798)=true := (hleft _ (by norm_num)).trans hmark
  have ho7 : out (-3797)=true := by simp [out,put,clearRange]
  have hcorr : ∀ q, -3797<q → q<3 → out q=false := by
    intro q hq hq'
    have hc : q= -3796 ∨ q= -3795 ∨ q= -3794 ∨ -3793≤q := by omega
    rcases hc with rfl | rfl | rfl | hlarge
    · simp [out,put,clearRange,h6]
    · simp [out,put,clearRange,h5]
    · simp [out,put,clearRange]
    · have hr : (-3793:Int)≤q ∧ q<4 := by omega
      have hn : q≠3 := by omega
      simp [out,put,clearRange,hr,hn]
  have hstop : out 3=true := by simp [out,put]
  have hedelim : e.tape 4=false := by
    have hh := (split_ones 3798 (-3794) e.tape [false] hrun).2
    simpa [Holds] using hh
  have hdelim : out 4=false := by
    have hh := near_carry_frame (-3824) 3793 e.tape 4 (Or.inr (by norm_num))
    norm_num at hh
    exact hh.trans hedelim
  have hall := segAdd machine _ _ _ _ 7603 hseg hcarry'
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbank',hpref,ho3,ho4,ho5,hray',ho8,ho7,hcorr,hstop,hdelim,hall⟩

/-- Retain the earlier finite-left-frame carry interface. -/
theorem blank_start_short_near_carry_with_frames :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ e.state=23 ∧
      let out := put (clearRange (put (put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
      Holds out 5 (encode (1::List.replicate 1897 0) ++ List.replicate 98 false) ∧
      Holds out (-3822) (zeroWord.take 24) ∧
      out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧
      out (-3798)=true ∧ out (-3797)=true ∧
      (∀ q, -3797<q → q<3 → out q=false) ∧ out 3=true ∧ out 4=false ∧
      silentSegment machine (machine.system.run 0) (cfg 83 (-3798) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbank,hpre,h3,h4,h5,_hray,h8,h7,hcorr,hstop,hdelim,hseg⟩ :=
    blank_start_short_near_carry_with_left_ray
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbank,hpre,h3,h4,h5,h8,h7,hcorr,hstop,hdelim,hseg⟩

/-- Retain the earlier reachable near-carry interface. -/
theorem blank_start_short_near_carry :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ e.state=23 ∧
      let out := put (clearRange (put (put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
      Holds out 5 (encode (1::List.replicate 1897 0)) ∧
      silentSegment machine (machine.system.run 0) (cfg 83 (-3798) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbank,_hray,hseg⟩ := blank_start_variable_unit_carry
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbank,by simpa [Nat.add_assoc] using hseg⟩

#print axioms blank_start_short_near_carry
end Shared.Beeping.NPcoNP.Bootstrap284ShortNearCarry
