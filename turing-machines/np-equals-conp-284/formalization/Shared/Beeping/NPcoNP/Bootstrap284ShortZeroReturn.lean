import Shared.Beeping.NPcoNP.Bootstrap284ShortZeroScan
import Shared.Beeping.NPcoNP.NativeFilledUnitWindow

/-! The literal return sweep after the shortened reachable zero selector. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284ShortZeroReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativePostAbsenceUnitScan
open Shared.Beeping.NPcoNP.NativeFilledUnitWindow
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284ShortZeroScan
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000
attribute [local irreducible] machine

/-- After the shortened scan, the actual machine returns to state 93 in
3,827 further silent steps, with the full next selector and bank. -/
theorem blank_start_short_zero_return_with_left_ray :
    ∃ (m n k j : Nat) (t : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      let out := fillRange (setAt (-3796) t) (-3794) 3
      Holds out (-3822) (markerWindow (List.replicate 11 0 ++ [1,0,3795])) ∧
      out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧ (∀ q, q≤ -3823 → out q=false) ∧ out (-3798)=true ∧
      out (-3797)=false ∧ out (-3795)=false ∧ out 2=true ∧ out 3=true ∧ out 4=false ∧
      Holds out 5 ((encode (List.replicate 1897 0) ++ [true,false,false]) ++ List.replicate 98 false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827) := by
  obtain ⟨m,n,k,j,t,hm,hn,hk,hj,hpre,habsent,hbefore,hextra,hray,hmark,hcorr,hstop,hdelim,hbank,hframe,hseg⟩ :=
    blank_start_short_zero_scan_with_left_ray
  let out := fillRange (setAt (-3796) t) (-3794) 3
  have hw := filled_unit_window (-3822) 3791 t hpre (by simpa using hmark) (by simpa using hcorr)
  have hw' : Holds out (-3822) (markerWindow (List.replicate 11 0 ++ [1,0,3795])) := by
    simpa [out,scanOutput] using hw
  let xs := List.replicate 11 0 ++ [1,0,3795]
  have hlen : (encode xs).length=3824 := by simp [xs,encode,block_length]
  have hs := marker_window_to92 out (-3822) xs (by simp [xs]) hw'
  rw [hlen] at hs
  have hs' : silentSegment machine (cfg 83 1 out) (cfg 92 (-3823) out) 3824 := by
    norm_num at hs ⊢
    exact hs
  have hz3 : out (-3823)=false := (hframe _ (Or.inl (by norm_num))).trans habsent
  have hray' : ∀ q, q≤ -3823 → out q=false := by
    intro q hq
    exact (hframe q (Or.inl (by omega))).trans (hray q hq)
  have hz4 : out (-3824)=false := (hframe _ (Or.inl (by norm_num))).trans hbefore
  have hz5left : out (-3825)=false := (hframe _ (Or.inl (by norm_num))).trans hextra
  have hz2 : out (-3822)=false := by
    have h := holds_get t (-3822) (zeroWord.take 24) hpre 0 (by decide)
    have hv : (zeroWord.take 24)[0]=false := by decide
    rw [hv] at h
    exact (hframe _ (Or.inl (by norm_num))).trans (by simpa using h)
  have ho1 : out (-3821)=true := by
    have h := holds_get t (-3822) (zeroWord.take 24) hpre 1 (by decide)
    have hv : (zeroWord.take 24)[1]=true := by decide
    rw [hv] at h
    exact (hframe _ (Or.inl (by norm_num))).trans (by simpa using h)
  have s1 : silentSegment machine (cfg 92 (-3823) out) (cfg 92 (-3822) out) 1 := by
    simpa using oneSeg machine _ _ (step92_zero (-3823) out hz3)
  have s2 : silentSegment machine (cfg 92 (-3822) out) (cfg 92 (-3821) out) 1 := by
    simpa using oneSeg machine _ _ (step92_zero (-3822) out hz2)
  have s3 : silentSegment machine (cfg 92 (-3821) out) (cfg 93 (-3820) out) 1 := by
    simpa using oneSeg machine _ _ (step92_one (-3821) out ho1)
  have s12 := segAdd machine _ _ _ 1 1 s1 s2
  have s123 := segAdd machine _ _ _ 2 1 s12 s3
  have ho8 : out (-3798)=true := (hframe _ (Or.inl (by norm_num))).trans hmark
  have hz7 : out (-3797)=false := by
    have hv := hcorr (-3797) (by norm_num) (by norm_num)
    simpa [out,fillRange,setAt] using hv
  have hz5 : out (-3795)=false := by
    have hv := hcorr (-3795) (by norm_num) (by norm_num)
    simpa [out,fillRange,setAt] using hv
  have htwo : out 2=true := by simp [out,fillRange]
  have hthree : out 3=true := (hframe 3 (Or.inr (by norm_num))).trans hstop
  have hfour : out 4=false := (hframe 4 (Or.inr (by norm_num))).trans hdelim
  have hback := segAdd machine _ _ _ 3824 3 hs' s123
  have hall := segAdd machine _ _ _ _ 3827 hseg (by simpa using hback)
  exact ⟨m,n,k,j,t,hm,hn,hk,hj,hw',hz3,hz4,hz5left,hray',ho8,hz7,hz5,htwo,hthree,hfour,hbank,hall⟩

/-- Retain the earlier marker-control return interface. -/
theorem blank_start_short_zero_return_with_marker :
    ∃ (m n k j : Nat) (t : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      let out := fillRange (setAt (-3796) t) (-3794) 3
      Holds out (-3822) (markerWindow (List.replicate 11 0 ++ [1,0,3795])) ∧
      out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧ out (-3798)=true ∧
      out (-3797)=false ∧ out (-3795)=false ∧ out 2=true ∧ out 3=true ∧ out 4=false ∧
      Holds out 5 ((encode (List.replicate 1897 0) ++ [true,false,false]) ++ List.replicate 98 false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827) := by
  obtain ⟨m,n,k,j,t,hm,hn,hk,hj,hw,h3,h4,h5,_hray,hmark,h7,hz5,h2,ht3,ht4,hbank,hseg⟩ :=
    blank_start_short_zero_return_with_left_ray
  exact ⟨m,n,k,j,t,hm,hn,hk,hj,hw,h3,h4,h5,hmark,h7,hz5,h2,ht3,ht4,hbank,hseg⟩

/-- Retain the earlier left-control interface. -/
theorem blank_start_short_zero_return_with_left :
    ∃ (m n k j : Nat) (t : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      let out := fillRange (setAt (-3796) t) (-3794) 3
      Holds out (-3822) (markerWindow (List.replicate 11 0 ++ [1,0,3795])) ∧
      out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧
      out (-3797)=false ∧ out (-3795)=false ∧ out 2=true ∧ out 3=true ∧ out 4=false ∧
      Holds out 5 ((encode (List.replicate 1897 0) ++ [true,false,false]) ++ List.replicate 98 false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827) := by
  obtain ⟨m,n,k,j,t,hm,hn,hk,hj,hw,h3,h4,h5,_hmk,h7,hz5,h2,ht3,ht4,hbank,hseg⟩ :=
    blank_start_short_zero_return_with_marker
  exact ⟨m,n,k,j,t,hm,hn,hk,hj,hw,h3,h4,h5,h7,hz5,h2,ht3,ht4,hbank,hseg⟩

/-- Retain the earlier carry-control interface. -/
theorem blank_start_short_zero_return_with_carry :
    ∃ (m n k j : Nat) (t : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      let out := fillRange (setAt (-3796) t) (-3794) 3
      Holds out (-3822) (markerWindow (List.replicate 11 0 ++ [1,0,3795])) ∧
      out (-3797)=false ∧ out (-3795)=false ∧ out 2=true ∧ out 3=true ∧ out 4=false ∧
      Holds out 5 ((encode (List.replicate 1897 0) ++ [true,false,false]) ++ List.replicate 98 false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827) := by
  obtain ⟨m,n,k,j,t,hm,hn,hk,hj,hw,_h3,_h4,_h5,hz7,hz5,h2,h3,h4,hbank,hseg⟩ :=
    blank_start_short_zero_return_with_left
  exact ⟨m,n,k,j,t,hm,hn,hk,hj,hw,hz7,hz5,h2,h3,h4,hbank,hseg⟩

/-- Retain the earlier extra-control interface. -/
theorem blank_start_short_zero_return_with_extra :
    ∃ (m n k j : Nat) (t : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      let out := fillRange (setAt (-3796) t) (-3794) 3
      Holds out (-3822) (markerWindow (List.replicate 11 0 ++ [1,0,3795])) ∧
      out (-3795)=false ∧ out 2=true ∧ out 3=true ∧ out 4=false ∧
      Holds out 5 ((encode (List.replicate 1897 0) ++ [true,false,false]) ++ List.replicate 98 false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827) := by
  obtain ⟨m,n,k,j,t,hm,hn,hk,hj,hw,_hz7,hz5,h2,h3,h4,hbank,hseg⟩ :=
    blank_start_short_zero_return_with_carry
  exact ⟨m,n,k,j,t,hm,hn,hk,hj,hw,hz5,h2,h3,h4,hbank,hseg⟩

/-- Retain the earlier reachable extension interface. -/
theorem blank_start_short_zero_return_with_extension :
    ∃ (m n k j : Nat) (t : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      let out := fillRange (setAt (-3796) t) (-3794) 3
      Holds out (-3822) (markerWindow (List.replicate 11 0 ++ [1,0,3795])) ∧
      out 2=true ∧ out 3=true ∧ out 4=false ∧
      Holds out 5 ((encode (List.replicate 1897 0) ++ [true,false,false]) ++ List.replicate 98 false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827) := by
  obtain ⟨m,n,k,j,t,hm,hn,hk,hj,hw,_hz5,h2,h3,h4,hbank,hseg⟩ :=
    blank_start_short_zero_return_with_extra
  exact ⟨m,n,k,j,t,hm,hn,hk,hj,hw,h2,h3,h4,hbank,hseg⟩

/-- Retain the earlier reachable return interface. -/
theorem blank_start_short_zero_return :
    ∃ (m n k j : Nat) (t : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      let out := fillRange (setAt (-3796) t) (-3794) 3
      Holds out (-3822) (markerWindow (List.replicate 11 0 ++ [1,0,3795])) ∧
      Holds out 5 ((encode (List.replicate 1897 0) ++ [true,false,false]) ++ List.replicate 98 false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827) := by
  obtain ⟨m,n,k,j,t,hm,hn,hk,hj,hw,_h2,_h3,_h4,hbank,hseg⟩ :=
    blank_start_short_zero_return_with_extension
  exact ⟨m,n,k,j,t,hm,hn,hk,hj,hw,hbank,hseg⟩

#print axioms blank_start_short_zero_return
end Shared.Beeping.NPcoNP.Bootstrap284ShortZeroReturn
