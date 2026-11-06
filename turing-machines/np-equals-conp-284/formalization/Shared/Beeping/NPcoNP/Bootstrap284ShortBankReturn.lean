import Shared.Beeping.NPcoNP.Bootstrap284ShortUnitIncrement
import Shared.Beeping.NPcoNP.NativeAllZeroNextReturn

/-! The shortened unit increment's bank return on the actual execution. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284ShortBankReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeAllZeroNextReturn
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284ShortUnitIncrement
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- After the shortened unit increment, the literal bank return reaches
state 1 in exactly 7,597 further silent transitions, without changing tape. -/
theorem blank_start_short_bank_return_with_left_ray :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      e.state=23 ∧ Holds e.tape 5 (encode (1::List.replicate 1897 0) ++ List.replicate 98 false) ∧
      Holds e.tape (-3822) (zeroWord.take 24) ∧
      e.tape (-3823)=false ∧ e.tape (-3824)=false ∧ e.tape (-3825)=false ∧
      (∀ q, q≤ -3823 → e.tape q=false) ∧ e.tape (-3798)=true ∧
      e.tape (-3797)=false ∧ e.tape (-3796)=false ∧ e.tape (-3795)=false ∧
      Holds e.tape (-3794) (List.replicate 3798 true ++ [false]) ∧
      silentSegment machine (machine.system.run 0) (cfg 1 (-3797) e.tape)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hh,hbank,hpre,h3,h4,h5,hray,hmark,h7,h0,h1,hrun,hseg⟩ :=
    blank_start_short_unit_increment_with_left_ray
  have hlen0 : (encode (List.replicate 1897 0)).length=3794 := by rw [zeros_length]
  have hlen : (encode (1::List.replicate 1897 0)).length=3797 := by
    simp only [encode,List.length_append,block_length,hlen0]
  have hbank0 := holds_prefix_word e.tape 5 (encode (1::List.replicate 1897 0)) (List.replicate 98 false) hbank
  have hret := bank_run_to1 1 (List.replicate 1897 0) (-3796) 3798 e.tape
    (by decide) h0 (by simpa using h1) (by simpa using hrun) (by simpa using hbank0)
  have hecfg : e=cfg 23 3800 e.tape := by
    have hc : e=cfg e.state e.head e.tape := by cases e; rfl
    simpa only [hs,hh] using hc
  have hret' : silentSegment machine e (cfg 1 (-3797) e.tape) 7597 := by
    simp only [hlen] at hret
    norm_num at hret
    simpa only [←hecfg] using hret
  have hall := segAdd machine _ _ _ _ 7597 hseg hret'
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbank,hpre,h3,h4,h5,hray,hmark,h7,h0,h1,hrun,hall⟩

/-- Retain the earlier marker-control bank-return interface. -/
theorem blank_start_short_bank_return_with_marker :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      e.state=23 ∧ Holds e.tape 5 (encode (1::List.replicate 1897 0) ++ List.replicate 98 false) ∧
      Holds e.tape (-3822) (zeroWord.take 24) ∧
      e.tape (-3823)=false ∧ e.tape (-3824)=false ∧ e.tape (-3825)=false ∧ e.tape (-3798)=true ∧
      e.tape (-3797)=false ∧ e.tape (-3796)=false ∧ e.tape (-3795)=false ∧
      Holds e.tape (-3794) (List.replicate 3798 true ++ [false]) ∧
      silentSegment machine (machine.system.run 0) (cfg 1 (-3797) e.tape)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbank,hpre,h3,h4,h5,_hray,hmark,h7,h0,h1,hrun,hseg⟩ :=
    blank_start_short_bank_return_with_left_ray
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbank,hpre,h3,h4,h5,hmark,h7,h0,h1,hrun,hseg⟩

/-- Retain the earlier framed bank-return interface. -/
theorem blank_start_short_bank_return_with_frames :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      e.state=23 ∧ Holds e.tape 5 (encode (1::List.replicate 1897 0) ++ List.replicate 98 false) ∧
      Holds e.tape (-3822) (zeroWord.take 24) ∧
      e.tape (-3823)=false ∧ e.tape (-3824)=false ∧ e.tape (-3825)=false ∧
      e.tape (-3797)=false ∧ e.tape (-3796)=false ∧ e.tape (-3795)=false ∧
      Holds e.tape (-3794) (List.replicate 3798 true ++ [false]) ∧
      silentSegment machine (machine.system.run 0) (cfg 1 (-3797) e.tape)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbank,hpre,h3,h4,h5,_hmark,h7,h0,h1,hrun,hseg⟩ :=
    blank_start_short_bank_return_with_marker
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbank,hpre,h3,h4,h5,h7,h0,h1,hrun,hseg⟩

/-- Retain the earlier carry-input bank-return interface. -/
theorem blank_start_short_bank_return_with_carry :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      e.state=23 ∧ Holds e.tape 5 (encode (1::List.replicate 1897 0)) ∧
      e.tape (-3797)=false ∧ e.tape (-3796)=false ∧ e.tape (-3795)=false ∧
      Holds e.tape (-3794) (List.replicate 3798 true ++ [false]) ∧
      silentSegment machine (machine.system.run 0) (cfg 1 (-3797) e.tape)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbank,_hp,_h3,_h4,_h5,h7,h0,h1,hrun,hseg⟩ :=
    blank_start_short_bank_return_with_frames
  have hb := holds_prefix_word e.tape 5 (encode (1::List.replicate 1897 0)) (List.replicate 98 false) hbank
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hb,h7,h0,h1,hrun,hseg⟩

/-- Retain the earlier reachable bank-return interface. -/
theorem blank_start_short_bank_return :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      e.state=23 ∧ Holds e.tape 5 (encode (1::List.replicate 1897 0)) ∧
      silentSegment machine (machine.system.run 0) (cfg 1 (-3797) e.tape)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbank,_h7,_h0,_h1,_hrun,hseg⟩ :=
    blank_start_short_bank_return_with_carry
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbank,hseg⟩

#print axioms blank_start_short_bank_return
end Shared.Beeping.NPcoNP.Bootstrap284ShortBankReturn
