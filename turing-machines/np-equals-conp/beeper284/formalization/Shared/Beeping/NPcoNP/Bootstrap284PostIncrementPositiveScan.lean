import Shared.Beeping.NPcoNP.Bootstrap284PostAbsenceIncrement
import Shared.Beeping.NPcoNP.NativePostIncrementPositiveScan

/-! The next positive selector scan on the actual blank-start execution.
This finite result does not establish the full graph/table simulation. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284PostIncrementPositiveScan
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact

open Shared.Beeping.NPcoNP.NativeHalfSweep

open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState10Exact

open Shared.Beeping.NPcoNP.NativeHalfSweep

open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativePostAbsenceUnitScan
open Shared.Beeping.NPcoNP.NativePostIncrementPositiveScan
open Shared.Beeping.NPcoNP.Bootstrap284PostAbsenceIncrement
open Shared.Beeping.NPcoNP.UnaryBank

set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- After the increment cycle, the blank-start run completes the next
state-260 scan in exactly 7,652 further silent transitions. -/
theorem blank_start_post_increment_roundtrip_with_left_ray :
    ∃ (m n k : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ e.state=23 ∧
      let t := put (clearRange (put (put e.tape (-3795) true) (-3792) false) (-3791) 4) 3 true
      let out := scanOutput (-3820) 3789 t
      Holds out 5 (encode (1::List.replicate 1896 0) ++ List.replicate 100 false) ∧
      Holds out (-3822) (markerWindow (List.replicate 12 0 ++ [3,3793])) ∧
      out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧
      (∀ q, q≤ -3823 → out q=false) ∧
      out 2=true ∧ out 3=true ∧ out 4=false ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652) := by
  obtain ⟨m,n,k,e,hm,hn,hk,hs,hbank,hpre,hleft,hleft0,habsent,hbefore,hextra,hray,h24,h25,hcorr,hstop,hdelim,hseg⟩ :=
    blank_start_post_absence_increment_cycle_with_left_ray
  let t := put (clearRange (put (put e.tape (-3795) true) (-3792) false) (-3791) 4) 3 true
  let out := scanOutput (-3820) 3789 t
  obtain ⟨hnext,hwindow,hframe⟩ := post_increment_roundtrip (-3820) 3789 t hpre
    (by simpa using hleft0) (by simpa using hleft) (by simpa using habsent)
    (by simpa using h24) (by simpa using h25) (by simpa using hcorr) (by simpa using hstop)
  have hbank' : Holds out 5 (encode (1::List.replicate 1896 0) ++ List.replicate 100 false) := by
    apply holds_transport t out _ _ hbank
    intro q hq _
    exact (hframe q (Or.inr (by norm_num at *; omega))).symm
  have hl3 : out (-3823)=false := (hframe _ (Or.inl (by norm_num))).trans habsent
  have hl4 : out (-3824)=false := (hframe _ (Or.inl (by norm_num))).trans hbefore
  have hl5 : out (-3825)=false := (hframe _ (Or.inl (by norm_num))).trans hextra
  have hray' : ∀ q, q≤ -3823 → out q=false := by
    intro q hq
    exact (hframe q (Or.inl (by omega))).trans (hray q hq)
  have htwo : out 2=true := by
    simp [out,scanOutput,fillRange]
  have hstop' : out 3=true := (hframe 3 (Or.inr (by norm_num))).trans hstop
  have hdelim' : out 4=false := (hframe 4 (Or.inr (by norm_num))).trans hdelim
  have hnext' : silentSegment machine (cfg 93 (-3820) t) (cfg 93 (-3820) out) 7652 := by
    norm_num at hnext ⊢
    exact hnext
  have hall := segAdd machine _ _ _ (2134479+m+29+n+(k+31)+30492) 7652 hseg hnext'
  exact ⟨m,n,k,e,hm,hn,hk,hs,hbank',by simpa using hwindow,hl3,hl4,hl5,hray',htwo,hstop',hdelim',hall⟩

/-- Retain the earlier finite-left-cell scan interface. -/
theorem blank_start_post_increment_roundtrip_with_left :
    ∃ (m n k : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ e.state=23 ∧
      let t := put (clearRange (put (put e.tape (-3795) true) (-3792) false) (-3791) 4) 3 true
      let out := scanOutput (-3820) 3789 t
      Holds out 5 (encode (1::List.replicate 1896 0) ++ List.replicate 100 false) ∧
      Holds out (-3822) (markerWindow (List.replicate 12 0 ++ [3,3793])) ∧
      out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧
      out 2=true ∧ out 3=true ∧ out 4=false ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652) := by
  obtain ⟨m,n,k,e,hm,hn,hk,hs,hbank,hwin,h3,h4,h5,_hray,h2,hstop,hdelim,hseg⟩ :=
    blank_start_post_increment_roundtrip_with_left_ray
  exact ⟨m,n,k,e,hm,hn,hk,hs,hbank,hwin,h3,h4,h5,h2,hstop,hdelim,hseg⟩

/-- Retain the earlier reachable scan interface. -/
theorem blank_start_post_increment_roundtrip :
    ∃ (m n k : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ e.state=23 ∧
      let t := put (clearRange (put (put e.tape (-3795) true) (-3792) false) (-3791) 4) 3 true
      let out := scanOutput (-3820) 3789 t
      Holds out 5 (encode (1::List.replicate 1896 0) ++ List.replicate 100 false) ∧
      Holds out (-3822) (markerWindow (List.replicate 12 0 ++ [3,3793])) ∧
      out 2=true ∧ out 3=true ∧ out 4=false ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652) := by
  obtain ⟨m,n,k,e,hm,hn,hk,hs,hbank,hwindow,_h3,_h4,_h5,h2,hstop,hdelim,hseg⟩ :=
    blank_start_post_increment_roundtrip_with_left
  exact ⟨m,n,k,e,hm,hn,hk,hs,hbank,hwindow,h2,hstop,hdelim,hseg⟩

#print axioms blank_start_post_increment_roundtrip
end Shared.Beeping.NPcoNP.Bootstrap284PostIncrementPositiveScan
