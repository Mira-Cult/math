import Shared.Beeping.NPcoNP.Bootstrap284PostAbsenceUnitScan
import Shared.Beeping.NPcoNP.Bootstrap284PostAbsenceLeftRay
import Shared.Beeping.NPcoNP.NativePostAbsenceIncrement

/-! Apply the post-absence increment to the checked blank-start execution.
This is a finite silent segment, not the full graph/table simulation. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284PostAbsenceIncrement
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativePostAbsenceIncrement
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284ReachableRecurrence
open Shared.Beeping.NPcoNP.Bootstrap284PostAbsenceLeftRay
open Shared.Beeping.NPcoNP.UnaryBank

set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- After the post-absence round trip, the actual unit increment and bank
return finish in exactly 22,861 further silent transitions. -/
theorem blank_start_post_absence_increment_return :
    ∃ (m n k : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ e.state=23 ∧
      Holds e.tape 5 (encode (1::List.replicate 1896 0)) ∧
      silentSegment machine (machine.system.run 0) (cfg 1 (-3795) e.tape)
        (2134479+m+29+n+(k+31)+22861) := by
  obtain ⟨m,n,k,t,hm,hn,hk,hbank,hpre,hleft,_h2,_h3,_h4,hmark,hcorr,hstop,hdelim,hseg⟩ :=
    blank_start_after_marker_absence_with_control
  have hvalues : 0::List.replicate 1896 0=List.replicate 1897 0 := by decide
  have hrep : List.replicate 101 false=[false] ++ List.replicate 100 false := by decide
  have hbank' : Holds t 5 (encode (0::List.replicate 1896 0) ++ [false]) := by
    rw [←hvalues,hrep,←List.append_assoc] at hbank
    exact holds_prefix_word t 5 (encode (0::List.replicate 1896 0) ++ [false])
      (List.replicate 100 false) hbank
  have hbank'' : Holds t ((-3820:Int)+36+(3789:Int))
      (encode (0::List.replicate 1896 0) ++ [false]) := by simpa using hbank'
  obtain ⟨e,hs,hnext,hebank,_hframe⟩ := post_absence_increment_return (-3820) 3789 0
    (List.replicate 1896 0) t hpre (by simpa using hleft) (by simpa using hmark)
    (by simpa using hcorr) (by simpa using hstop) (by simpa using hdelim) hbank''
  have hlen : (encode (List.replicate 1896 0)).length=3792 := by rw [zeros_length]
  have hlen' : (encode ((0+1)::List.replicate 1896 0)).length=3795 := by
    simp only [encode,List.length_append,block_length,hlen]
  have hnext' : silentSegment machine (cfg 93 (-3820) t) (cfg 1 (-3795) e.tape) 22861 := by
    simp only [hlen,hlen'] at hnext
    norm_num at hnext ⊢
    exact hnext
  have hall := segAdd machine _ _ _ (2134479+m+29+n+(k+31)) 22861 hseg hnext'
  exact ⟨m,n,k,e,hm,hn,hk,hs,by simpa using hebank,hall⟩

/-- The actual execution completes the increment, carry and redispatch in
30,492 silent transitions from the proved post-absence control state. -/
theorem blank_start_post_absence_increment_cycle_with_left_ray :
    ∃ (m n k : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ e.state=23 ∧
      let out := put (clearRange (put (put e.tape (-3795) true) (-3792) false) (-3791) 4) 3 true
      Holds out 5 (encode (1::List.replicate 1896 0) ++ List.replicate 100 false) ∧
      Holds out (-3820) (zeroWord.take 24) ∧
      out (-3821)=true ∧ out (-3822)=false ∧ out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧
      (∀ q, q≤ -3823 → out q=false) ∧
      out (-3796)=true ∧ out (-3795)=true ∧
      (∀ q, -3795<q → q<3 → out q=false) ∧ out 3=true ∧ out 4=false ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492) := by
  obtain ⟨m,n,k,t,hm,hn,hk,hbank,hpre,hleft,hleft0,habsent,hbefore,hextra,hray,hmark,hcorr,hstop,hdelim,hseg⟩ :=
    blank_start_after_marker_absence_with_left_ray
  have hvalues : 0::List.replicate 1896 0=List.replicate 1897 0 := by decide
  have hrep : List.replicate 101 false=[false] ++ List.replicate 100 false := by decide
  have hbank' : Holds t 5 (encode (0::List.replicate 1896 0) ++ [false]) := by
    rw [←hvalues,hrep,←List.append_assoc] at hbank
    exact holds_prefix_word t 5 (encode (0::List.replicate 1896 0) ++ [false])
      (List.replicate 100 false) hbank
  have hbank'' : Holds t ((-3820:Int)+36+(3789:Int))
      (encode (0::List.replicate 1896 0) ++ [false]) := by simpa using hbank'
  obtain ⟨e,hs,hnext,hebank,hemark,hemark2,hecorr,hestop,hedelim,heframe,heright⟩ :=
    post_absence_increment_cycle_with_frame (-3820) 3789 0 (List.replicate 1896 0) t hpre
      (by simpa using hleft) (by simpa using hleft0) (by simpa using habsent) (by simpa using hbefore)
      (by simpa using hmark) (by simpa using hcorr) (by simpa using hstop) (by simpa using hdelim) hbank''
  let out := put (clearRange (put (put e.tape (-3795) true) (-3792) false) (-3791) 4) 3 true
  have hlen : (encode (List.replicate 1896 0)).length=3792 := by rw [zeros_length]
  have hlen' : (encode ((0+1)::List.replicate 1896 0)).length=3795 := by
    simp only [encode,List.length_append,block_length,hlen]
  have htail : Holds t (5+((encode (0::List.replicate 1896 0) ++ [false]).length : Int))
      (List.replicate 100 false) :=
    holds_append_tail t 5 (encode (0::List.replicate 1896 0) ++ [false]) (List.replicate 100 false) hbank
  have hlen0 : (encode (0::List.replicate 1896 0)).length=3794 := by
    simp only [encode,List.length_append,block_length,hlen]
  have htail' : Holds out (5+((encode (1::List.replicate 1896 0)).length : Int))
      (List.replicate 100 false) := by
    have hp : 5+((encode (1::List.replicate 1896 0)).length : Int)=
        5+((encode (0::List.replicate 1896 0) ++ [false]).length : Int) := by
      simp only [List.length_append,List.length_cons,List.length_nil,hlen0,hlen']
    rw [hp]
    apply holds_transport t out _ _ htail
    intro q hq _
    symm
    apply heright q
    simp only [List.length_append,List.length_cons,List.length_nil,hlen0] at hq
    simp only [hlen]
    norm_num at hq ⊢
    omega
  have hbankfull : Holds out 5 (encode (1::List.replicate 1896 0) ++ List.replicate 100 false) :=
    holds_append_intro out 5 (encode (1::List.replicate 1896 0)) (List.replicate 100 false) hebank htail'
  have hnext' : silentSegment machine (cfg 93 (-3820) t) (cfg 93 (-3820) out) 30492 := by
    simp only [hlen,hlen'] at hnext
    norm_num at hnext ⊢
    exact hnext
  have hpref : Holds out (-3820) (zeroWord.take 24) := by
    apply holds_transport t out _ _ hpre
    intro q _ hq
    have hl : (zeroWord.take 24).length=24 := by decide
    rw [hl] at hq
    exact (heframe q (by omega)).symm
  have hh1 : out (-3821)=true := (heframe _ (by norm_num)).trans hleft
  have hh2 : out (-3822)=false := (heframe _ (by norm_num)).trans hleft0
  have hh3 : out (-3823)=false := (heframe _ (by norm_num)).trans habsent
  have hh4 : out (-3824)=false := (heframe _ (by norm_num)).trans hbefore
  have hh5 : out (-3825)=false := (heframe _ (by norm_num)).trans hextra
  have hray' : ∀ q, q≤ -3823 → out q=false := by
    intro q hq
    have hh : out q=t q := by simpa using heframe q (by omega)
    exact hh.trans (hray q hq)
  have hall := segAdd machine _ _ _ (2134479+m+29+n+(k+31)) 30492 hseg hnext'
  exact ⟨m,n,k,e,hm,hn,hk,hs,hbankfull,hpref,hh1,hh2,hh3,hh4,hh5,hray',
    by simpa using hemark,by simpa using hemark2,by simpa using hecorr,
    by simpa using hestop,by simpa using hedelim,hall⟩

/-- Retain the earlier extra-left-cell interface. -/
theorem blank_start_post_absence_increment_cycle_with_extra :
    ∃ (m n k : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ e.state=23 ∧
      let out := put (clearRange (put (put e.tape (-3795) true) (-3792) false) (-3791) 4) 3 true
      Holds out 5 (encode (1::List.replicate 1896 0) ++ List.replicate 100 false) ∧
      Holds out (-3820) (zeroWord.take 24) ∧
      out (-3821)=true ∧ out (-3822)=false ∧ out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧
      out (-3796)=true ∧ out (-3795)=true ∧
      (∀ q, -3795<q → q<3 → out q=false) ∧ out 3=true ∧ out 4=false ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492) := by
  obtain ⟨m,n,k,e,hm,hn,hk,hs,hbank,hpre,h1,h2,h3,h4,h5,_hray,hmark,hmark2,hcorr,hstop,hdelim,hseg⟩ :=
    blank_start_post_absence_increment_cycle_with_left_ray
  exact ⟨m,n,k,e,hm,hn,hk,hs,hbank,hpre,h1,h2,h3,h4,h5,hmark,hmark2,hcorr,hstop,hdelim,hseg⟩

/-- Retain the earlier padded increment-cycle interface. -/
theorem blank_start_post_absence_increment_cycle_with_padding :
    ∃ (m n k : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ e.state=23 ∧
      let out := put (clearRange (put (put e.tape (-3795) true) (-3792) false) (-3791) 4) 3 true
      Holds out 5 (encode (1::List.replicate 1896 0) ++ List.replicate 100 false) ∧
      Holds out (-3820) (zeroWord.take 24) ∧
      out (-3821)=true ∧ out (-3822)=false ∧ out (-3823)=false ∧ out (-3824)=false ∧
      out (-3796)=true ∧ out (-3795)=true ∧
      (∀ q, -3795<q → q<3 → out q=false) ∧ out 3=true ∧ out 4=false ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492) := by
  obtain ⟨m,n,k,e,hm,hn,hk,hs,hbank,hpre,h1,h2,h3,h4,_h5,hmark,hmark2,hcorr,hstop,hdelim,hseg⟩ :=
    blank_start_post_absence_increment_cycle_with_extra
  exact ⟨m,n,k,e,hm,hn,hk,hs,hbank,hpre,h1,h2,h3,h4,hmark,hmark2,hcorr,hstop,hdelim,hseg⟩

/-- Retain the earlier reachable increment-cycle interface. -/
theorem blank_start_post_absence_increment_cycle :
    ∃ (m n k : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ e.state=23 ∧
      let out := put (clearRange (put (put e.tape (-3795) true) (-3792) false) (-3791) 4) 3 true
      Holds out 5 (encode (1::List.replicate 1896 0)) ∧
      Holds out (-3820) (zeroWord.take 24) ∧
      out (-3821)=true ∧ out (-3822)=false ∧ out (-3823)=false ∧ out (-3824)=false ∧
      out (-3796)=true ∧ out (-3795)=true ∧
      (∀ q, -3795<q → q<3 → out q=false) ∧ out 3=true ∧ out 4=false ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492) := by
  obtain ⟨m,n,k,e,hm,hn,hk,hs,hbank,hpre,h1,h2,h3,h4,hmark,hmark2,hcorr,hstop,hdelim,hseg⟩ :=
    blank_start_post_absence_increment_cycle_with_padding
  have hb := holds_prefix_word _ 5 (encode (1::List.replicate 1896 0)) (List.replicate 100 false) hbank
  exact ⟨m,n,k,e,hm,hn,hk,hs,hb,hpre,h1,h2,h3,h4,hmark,hmark2,hcorr,hstop,hdelim,hseg⟩

#print axioms blank_start_post_absence_increment_return
#print axioms blank_start_post_absence_increment_cycle
#print axioms blank_start_post_absence_increment_cycle_with_padding
end Shared.Beeping.NPcoNP.Bootstrap284PostAbsenceIncrement
