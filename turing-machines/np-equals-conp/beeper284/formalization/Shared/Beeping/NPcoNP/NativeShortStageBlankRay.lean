import Shared.Beeping.NPcoNP.NativeShortCycleStage
import Shared.Beeping.NPcoNP.NativeVariableUnitRightFrame
import Shared.Beeping.NPcoNP.NativeVariablePositiveRightFrame
import Shared.Beeping.NPcoNP.NativeAllBankDecrementPadding
import Shared.Beeping.NPcoNP.NativeVariableZeroToUnit
import Shared.Beeping.NPcoNP.NativeVariablePositiveRoundtrip
import Shared.Beeping.NPcoNP.NativeVariablePositiveRedispatch

/-! Explicit physical stages for a shortened selector cycle. These predicates
are local tape layouts, not the global register-graph invariant. -/
namespace Shared.Beeping.NPcoNP.NativeShortStageBlankRay
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeVariableZeroToUnit
open Shared.Beeping.NPcoNP.NativeVariableUnitRedispatch
open Shared.Beeping.NPcoNP.NativeVariableUnitRightFrame
open Shared.Beeping.NPcoNP.NativeShortCycleStage
open Shared.Beeping.NPcoNP.NativeVariablePositiveRoundtrip
open Shared.Beeping.NPcoNP.NativeVariablePositiveRedispatch
open Shared.Beeping.NPcoNP.NativeVariablePositiveRightFrame
open Shared.Beeping.NPcoNP.NativeAllBankDecrementPadding
open Shared.Beeping.NPcoNP.NativeVariableUnitCarry
open Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

def ZeroRay (a : Int) (k s v : Nat) (rest : List Nat) (t : Int → Bool) : Prop :=
  ∀ q, controlBank a k s+((encode (v::rest)).length : Int)+1≤q → t q=false

def PositiveRay (a : Int) (k s v : Nat) (rest : List Nat) (t : Int → Bool) : Prop :=
  ∀ q, controlBank a k s+((encode ((v+1)::rest)).length : Int)≤q → t q=false

theorem short_stage_to_positive_with_ray (t : Int → Bool) (a : Int) (k s v : Nat)
    (rest : List Nat) (pad : List Bool) (hk : k≤10)
    (stage : ShortStage a k s v rest ([false,false] ++ pad) t)
    (ray : ZeroRay a k s v rest t) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=23 ∧
      let d := controlD a k
      let out := put (clearRange (put (put e.tape (d-1) true) (d+2) false)
        (d+3) (d+((s+7 : Nat):Int))) (d+((s+6 : Nat):Int)) true
      ShortPositiveStage a k s v (rest ++ [0]) pad out ∧
      PositiveRay a k s v (rest ++ [0]) out ∧
      silentSegment machine (cfg 93 a t) (cfg 93 a out) n := by
  obtain ⟨hzero,hwindow,hprefix,hblank,hmark,hzero0,hzero1,hrun,hbank⟩ :=
    variable_zero_to_unit t a k s v rest ([false,false] ++ pad) hk stage.window stage.blank stage.left0 stage.left1
      (by
        have hp : controlD a k-2=a+((2*k : Nat):Int)+2 := by dsimp [controlD]; omega
        simpa only [hp] using stage.mark) (by
        intro q hq hq'
        apply stage.corridor <;> dsimp [controlD,controlStop] <;> omega)
      (by simpa [controlD,controlStop] using stage.stop) (by
        have hp : controlStop a k s+1=a+((2*k : Nat):Int)+4+((s+7 : Nat):Int) := by
          simp only [controlStop,controlD]; push_cast; omega
        simpa only [hp] using stage.delim) (by simpa [controlBank,controlD] using stage.bank)
  let d := controlD a k
  let t1 := fillRange (setAt d t) (d+2) (d+2+((s+4 : Nat):Int))
  have hzero' : silentSegment machine (cfg 93 a t) (cfg 93 a t1) (2*k+2*s+46) := by
    simpa only [controlD,d,t1] using hzero
  have hwindow' : Holds t1 a (markerWindow (List.replicate k 0 ++ 1::0::(s+2)::[])) := by
    simpa only [controlD,d,t1] using hwindow
  have hprefix' : Holds t1 (a-2) (zeroPairs (k+2)) := by simpa only [controlD,d,t1] using hprefix
  have hblank' : ∀ q, q<a-2 → t1 q=false := by simpa only [controlD,d,t1] using hblank
  have hmark' : t1 (a+((2*k : Nat):Int)+2)=true := by simpa only [controlD,d,t1] using hmark
  have hzero0' : t1 (a+((2*k : Nat):Int)+3)=false := by simpa only [controlD,d,t1] using hzero0
  have hzero1' : t1 (a+((2*k : Nat):Int)+5)=false := by simpa only [controlD,d,t1] using hzero1
  have hrun' : Holds t1 (a+((2*k : Nat):Int)+6) (List.replicate (s+5) true ++ [false]) := by
    simpa only [controlD,d,t1] using hrun
  have hbank' : Holds t1 (a+((2*k : Nat):Int)+4+((s+8 : Nat):Int))
      ((encode (v::(rest ++ [0])) ++ [false]) ++ ([false,false] ++ pad)) := by
    simpa only [controlD,d,t1] using hbank
  obtain ⟨e,hs,hebank,hewin,he0,he1,heblank,hemark,henext,hecorr,hestop,hedelim,heright,hnext⟩ :=
    variable_unit_carry_redispatch_with_right_frame t1 a k (s+2) s v [] (rest ++ [0]) ([false,false] ++ pad) (by omega)
      hwindow' hprefix' hblank' hmark' hzero0' hzero1' hrun' hbank'
  let out := put (clearRange (put (put e.tape (d-1) true) (d+2) false)
    (d+3) (d+((s+7 : Nat):Int))) (d+((s+6 : Nat):Int)) true
  have hstage : ShortPositiveStage a k s v (rest ++ [0]) pad out := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [controlD,d,out] using hewin
    · simpa only [controlD,d,out] using heblank
    · simpa only [controlD,d,out] using he0
    · simpa only [controlD,d,out] using he1
    · simpa only [controlD,d,out] using hemark
    · simpa only [controlD,d,out] using henext
    · simpa only [controlD,controlStop,d,out] using hecorr
    · simpa only [controlD,controlStop,d,out] using hestop
    · have hp : controlStop a k s+1=d+((s+7 : Nat):Int) := by dsimp [controlStop,d]; push_cast; omega
      simpa only [hp,controlD,d,out] using hedelim
    · simpa only [controlBank,controlD,d,out,List.append_assoc] using hebank
  have hray : PositiveRay a k s v (rest ++ [0]) out := by
    intro q hq
    have hlen : (encode ((v+1)::(rest ++ [0]))).length = (encode (v::rest)).length+3 := by
      simp only [encode,encode_append,List.length_append,block_length,List.length_nil,List.nil_append]
      omega
    have hlenR : (encode (rest++[0])).length=(encode rest).length+2 := by
      rw [append_zero_block]
      simp only [List.length_append,List.length_cons,List.length_nil]
    have hlenOld : (encode (v::rest)).length=v+2+(encode rest).length := by
      change (block v ++ encode rest).length=_
      rw [List.length_append,block_length]
    have hthreshold : a+((2*k : Nat):Int)+4+((s+8 : Nat):Int)+
        (((v+1)+(encode (rest++[0])).length : Nat):Int)<q := by
      have hh := hq
      rw [hlen] at hh
      dsimp [controlBank,controlD] at hh
      rw [hlenOld] at hh
      rw [hlenR]
      push_cast at hh ⊢
      omega
    have hf : out q=t1 q := by simpa only [controlD,d,out] using heright q hthreshold
    rw [hf]
    have hfar : d+2+((s+4 : Nat):Int)≤q := by
      dsimp [controlBank,controlD,d] at hq ⊢
      simp only [hlen] at hq
      push_cast at hq ⊢
      have hnon : 0≤((encode (v::rest)).length : Int) := by omega
      omega
    have hn : q≠d := by omega
    have heq : t1 q=t q := by
      simp only [t1,fillRange,setAt]
      split_ifs <;> first | omega | rfl
    rw [heq]
    apply ray
    dsimp [ZeroRay,controlBank,controlD] at *
    rw [hlen] at hq
    push_cast at hq ⊢
    omega
  let n := (2*k+2*s+46)+
    ((((2*k+6)+(s+6)+(v+3+(encode (rest ++ [0])).length))+
      ((encode ((v+1)::(rest ++ [0]))).length+(s+5)+2)+(2*s+17))+32)
  have hnext' : silentSegment machine (cfg 93 a t1) (cfg 93 a out)
      ((((2*k+6)+(s+6)+(v+3+(encode (rest ++ [0])).length))+
        ((encode ((v+1)::(rest ++ [0]))).length+(s+5)+2)+(2*s+17))+32) := by
    simpa only [controlD,d,out] using hnext
  have hall := segAdd machine _ _ _ (2*k+2*s+46) _ hzero' hnext'
  exact ⟨n,e,by dsimp [n]; omega,hs,hstage,hray,hall⟩


theorem short_positive_to_next_with_ray (t : Int → Bool) (a : Int) (k s v : Nat)
    (rest : List Nat) (pad : List Bool) (hk : 0<k) (hk10 : k≤10)
    (stage : ShortPositiveStage a k s v rest pad t)
    (ray : PositiveRay a k s v rest t) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      ShortStage a (k-1) (s+2) v rest pad out ∧
      ZeroRay a (k-1) (s+2) v rest out ∧
      silentSegment machine (cfg 93 a t) (cfg 93 a out) n := by
  let d := controlD a k
  let stopPos := controlStop a k s
  let x := controlBank a k s
  have hmark : t (a+((2*k : Nat):Int)+2)=true := by
    have hp : d-2=a+((2*k : Nat):Int)+2 := by dsimp [d,controlD]; omega
    simpa only [hp,d] using stage.mark
  have hnext : t (a+((2*k : Nat):Int)+3)=true := by
    have hp : d-1=a+((2*k : Nat):Int)+3 := by dsimp [d,controlD]; omega
    simpa only [hp,d] using stage.next
  have h0 : t (a+((2*k : Nat):Int)+4)=false := by
    apply stage.corridor <;> dsimp [controlD,controlStop] <;> omega
  have h1 : t (a+((2*k : Nat):Int)+5)=false := by
    apply stage.corridor <;> dsimp [controlD,controlStop] <;> omega
  have hzeros : ∀ i : Nat, i<(s+2)+2 → t (a+((2*k : Nat):Int)+6+(i : Int))=false := by
    intro i hi
    apply stage.corridor <;> dsimp [controlD,controlStop] <;> omega
  have hstop : t (a+((2*k : Nat):Int)+6+(((s+2)+2 : Nat):Int))=true := by
    have hp : a+((2*k : Nat):Int)+6+(((s+2)+2 : Nat):Int)=controlStop a k s := by
      dsimp [controlStop,controlD]; push_cast; omega
    simpa only [hp] using stage.stop
  obtain ⟨hscan,hwindow,hframe⟩ := variable_positive_roundtrip t a k (s+2) (by omega)
    stage.window stage.blank stage.left0 stage.left1 hmark hnext h0 h1 hzeros hstop
  let t1 := fillRange (setAt d t) (d+2) (d+2+((s+4 : Nat):Int))
  have hpstop : d+2+((s+4 : Nat):Int)=stopPos := by dsimp [stopPos,controlStop,d]; push_cast; omega
  have hscan' : silentSegment machine (cfg 93 a t) (cfg 93 a t1) (2*k+2*s+48) := by
    have hc : 2*k+2*(s+2)+44=2*k+2*s+48 := by omega
    simpa only [d,controlD,t1,hc,show s+2+2=s+4 by omega] using hscan
  have hf : ∀ q, q<d ∨ stopPos≤q → t1 q=t q := by
    have he : a+((2*k : Nat):Int)+4+2+(((s+2)+2 : Nat):Int)=stopPos := by
      dsimp [stopPos,controlStop,controlD]; push_cast; omega
    rw [he] at hframe
    simpa only [d,controlD,t1,he,show s+2+2=s+4 by omega] using hframe
  have hw : Holds t1 (a-2) (markerWindow (List.replicate (k+1) 0 ++ [3,s+2])) := by
    simpa only [d,controlD,t1] using hwindow
  have hblank : ∀ q, q<a-2 → t1 q=false := by
    intro q hq
    exact (hf q (Or.inl (by dsimp [d,controlD]; omega))).trans (stage.blank q hq)
  have hstop' : t1 stopPos=true := (hf _ (Or.inr (by omega))).trans stage.stop
  have hdelim' : t1 (stopPos+1)=false := (hf _ (Or.inr (by omega))).trans (by simpa [stopPos] using stage.delim)
  have hbefore : t1 (stopPos-1)=true := by
    have hr : d+2≤stopPos-1 ∧ stopPos-1<d+2+((s+4 : Nat):Int) := by
      rw [hpstop]; dsimp [stopPos,controlStop,d,controlD]; push_cast; omega
    simp [t1,fillRange,hr] <;> omega
  have hlen : (encode (List.replicate k 0 ++ [3,s+2])).length=2*k+s+9 := by
    simp [encode_append,encode,zeros_length,block_length]
    omega
  have hext : Holds t1 (a+((encode (List.replicate k 0 ++ [3,s+2])).length : Int)) [true,true,false] := by
    have hp : a+((encode (List.replicate k 0 ++ [3,s+2])).length : Int)=stopPos-1 := by
      rw [hlen]; dsimp [stopPos,controlStop,d,controlD]; push_cast; omega
    rw [hp]
    simp only [Holds]
    refine ⟨hbefore,?_,?_,trivial⟩
    · simpa only [show stopPos-1+1=stopPos by omega] using hstop'
    · simpa only [show stopPos-1+1+1=stopPos+1 by omega] using hdelim'
  have hbank : Holds t1 (a+((2*k : Nat):Int)+4+((s+2 : Nat):Int)+2+4)
      ((encode ((v+1)::rest) ++ [false,false]) ++ pad) := by
    have hp : a+((2*k : Nat):Int)+4+((s+2 : Nat):Int)+2+4=x := by dsimp [x,controlBank,controlD]; push_cast; omega
    rw [hp]
    apply holds_transport t t1 _ _ (by simpa [x] using stage.bank)
    intro q hq _
    exact (hf q (Or.inr (by dsimp [x,controlBank,stopPos,controlStop] at hq ⊢; omega))).symm
  obtain ⟨m,out,hm,hpairs,hleft0,hleft1,hblank',hmarker,hdelim,hbank',hcorr,hstop'',hright,hnext'⟩ :=
    variable_positive_bank_redispatch_with_right_frame t1 a k (s+2) v rest pad (by omega) hw hblank hext hbank
  have hd : controlD a (k-1)=d-2 := by
    have hn : k-1+1=k := by omega
    have hi : ((k-1 : Nat):Int)+1=(k : Int) := by exact_mod_cast hn
    dsimp [controlD,d]; push_cast; omega
  have hstopEq : controlStop a (k-1) (s+2)=stopPos := by
    dsimp [controlStop,stopPos]
    rw [hd]
    dsimp [d,controlD]
    push_cast
    omega
  have hbankEq : controlBank a (k-1) (s+2)=x := by
    dsimp [controlBank,x]
    rw [hd]
    dsimp [d,controlD]
    push_cast
    omega
  have hwin : Holds out a (markerWindow (List.replicate (k-1) 0 ++ [0])) := by
    have he : markerWindow (List.replicate (k-1) 0 ++ [0])=zeroPairs k := by
      rw [zero_window_pairs]
      have hk' : k-1+1=k := by omega
      rw [hk']
    simpa only [he] using hpairs
  have hstage : ShortStage a (k-1) (s+2) v rest pad out := by
    refine ⟨hwin,hblank',hleft0,hleft1,?_,?_,?_,?_,?_⟩
    · have hp : controlD a (k-1)-2=a+((2*k : Nat):Int)+4-4 := by rw [hd]; dsimp [d,controlD]; omega
      simpa only [hp] using hmarker
    · intro q hq hq'
      apply hcorr
      · rw [hd] at hq
        dsimp [d,controlD] at hq ⊢
        omega
      · rw [hstopEq] at hq'
        dsimp [stopPos,controlStop,d,controlD] at hq' ⊢
        push_cast at hq' ⊢
        omega
    · rw [hstopEq]
      have hp : stopPos=a+((2*k : Nat):Int)+4+((s+2 : Nat):Int)+2+4-2 := by
        dsimp [stopPos,controlStop,d,controlD]; push_cast; omega
      simpa only [hp] using hstop''
    · rw [hstopEq]
      have hp : stopPos+1=a+((2*k : Nat):Int)+4+((s+2 : Nat):Int)+2+4-1 := by
        dsimp [stopPos,controlStop,d,controlD]; push_cast; omega
      simpa only [hp] using hdelim
    · rw [hbankEq]
      have hp : a+((2*k : Nat):Int)+4+((s+2 : Nat):Int)+2+4=x := by
        dsimp [x,controlBank,controlD]; push_cast; omega
      simpa only [hp] using hbank'
  have hray : ZeroRay a (k-1) (s+2) v rest out := by
    intro q hq
    have he : (encode ((v+1)::rest)).length=(encode (v::rest)).length+1 := by
      change (block (v+1) ++ encode rest).length=(block v ++ encode rest).length+1
      simp only [List.length_append,block_length]
      omega
    have hflat := flat_length rest
    have hbanklen : (encode (v::rest)).length=v+2+(encode rest).length := by
      change (block v ++ encode rest).length=_
      rw [List.length_append,block_length]
    have hq' : x+((encode (v::rest)).length : Int)+1≤q := by
      rw [hbankEq] at hq
      exact hq
    have hthreshold : a+((2*k : Nat):Int)+4+((s+2 : Nat):Int)+2+4+2+
        ((List.replicate v true ++ rest.flatMap (fun z => false :: List.replicate (z+1) true)).length : Int)<q := by
      simp only [List.length_append,List.length_replicate,hflat]
      rw [hbanklen] at hq'
      dsimp [x,controlBank,controlD] at hq'
      push_cast at hq' ⊢
      omega
    have heout : out q=t1 q := hright q hthreshold
    rw [heout,hf q (Or.inr (by
      dsimp [x,controlBank,stopPos,controlStop] at hq' ⊢
      have hnon : 0≤((encode (v::rest)).length:Int) := by omega
      omega))]
    apply ray
    rw [he]
    push_cast
    dsimp only [x] at hq'
    omega
  let n := (2*k+2*s+48)+(m+31)
  have hall := segAdd machine _ _ _ (2*k+2*s+48) (m+31) hscan' hnext'
  exact ⟨n,out,by dsimp [n]; omega,hstage,hray,hall⟩


theorem short_stage_step_with_ray (t : Int → Bool) (a : Int) (k s v : Nat)
    (rest : List Nat) (pad : List Bool) (hk : 0<k) (hk10 : k≤10)
    (stage : ShortStage a k s v rest ([false,false] ++ pad) t)
    (ray : ZeroRay a k s v rest t) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      ShortStage a (k-1) (s+2) v (rest ++ [0]) pad out ∧
      ZeroRay a (k-1) (s+2) v (rest ++ [0]) out ∧
      silentSegment machine (cfg 93 a t) (cfg 93 a out) n := by
  obtain ⟨n,e,hn,_,hpos,hposray,hfirst⟩ := short_stage_to_positive_with_ray t a k s v rest pad hk10 stage ray
  let d := controlD a k
  let mid := put (clearRange (put (put e.tape (d-1) true) (d+2) false)
    (d+3) (d+((s+7 : Nat):Int))) (d+((s+6 : Nat):Int)) true
  have hpos' : ShortPositiveStage a k s v (rest ++ [0]) pad mid := by
    simpa only [mid,d] using hpos
  have hfirst' : silentSegment machine (cfg 93 a t) (cfg 93 a mid) n := by
    simpa only [mid,d] using hfirst
  have hposray' : PositiveRay a k s v (rest ++ [0]) mid := by
    simpa only [mid,d] using hposray
  obtain ⟨m,out,hm,hstage,hray,hsecond⟩ :=
    short_positive_to_next_with_ray mid a k s v (rest ++ [0]) pad hk hk10 hpos' hposray'
  exact ⟨n+m,out,by omega,hstage,hray,segAdd machine _ _ _ n m hfirst' hsecond⟩


#print axioms short_stage_step_with_ray
#print axioms short_positive_to_next_with_ray
#print axioms short_stage_to_positive_with_ray
end Shared.Beeping.NPcoNP.NativeShortStageBlankRay
