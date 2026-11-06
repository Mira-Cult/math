import Shared.Beeping.NPcoNP.NativeShortCycleStage

/-! The zero-leading-block boundary of the local positive stage. -/
namespace Shared.Beeping.NPcoNP.NativeShortCycleTerminal
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
open Shared.Beeping.NPcoNP.NativeVariablePositiveRoundtrip
open Shared.Beeping.NPcoNP.NativeVariablePositiveRedispatch
open Shared.Beeping.NPcoNP.NativeVariableUnitCarry
open Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.NativeShortCycleStage
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

/-- The positive scan and bank redispatch also work with zero leading
selector blocks. Its output has a marker at the scan head. -/
theorem short_positive_terminal (t : Int → Bool) (a : Int) (s v : Nat)
    (rest : List Nat) (pad : List Bool)
    (stage : ShortPositiveStage a 0 s v rest pad t) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      out (a-2)=false ∧ out (a-1)=true ∧ (∀ q, q<a-2 → out q=false) ∧
      out a=true ∧ (∀ q, a<q → q<controlStop a 0 s → out q=false) ∧
      out (controlStop a 0 s)=true ∧ out (controlStop a 0 s+1)=false ∧
      Holds out (controlBank a 0 s) ((encode (v::rest) ++ [true,false,false]) ++ pad) ∧
      silentSegment machine (cfg 93 a t) (cfg 93 a out) n := by
  let k : Nat := 0
  have hk10 : k≤10 := by simp [k]
  have stage : ShortPositiveStage a k s v rest pad t := stage
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
  obtain ⟨m,out,hm,hpairs,hleft0,hleft1,hblank',hmarker,hdelim,hbank',hcorr,hstop'',hnext'⟩ :=
    variable_positive_bank_redispatch t1 a k (s+2) v rest pad (by omega) hw hblank hext hbank
  have hall := segAdd machine _ _ _ (2*k+2*s+48) (m+31) hscan' hnext'
  refine ⟨_,out,by omega,hleft0,hleft1,hblank',?_,?_,?_,?_,?_,hall⟩
  · simpa [k,controlD] using hmarker
  · intro q hqa hqs
    apply hcorr
    · simpa [k] using hqa
    · dsimp [k,controlD,controlStop] at hqs ⊢; push_cast at hqs ⊢; omega
  · have hp : a+((2*k : Nat):Int)+4+((s+2 : Nat):Int)+2+4-2=controlStop a 0 s := by
      dsimp [k,controlD,controlStop]; push_cast; omega
    simpa only [hp] using hstop''
  · have hp : a+((2*k : Nat):Int)+4+((s+2 : Nat):Int)+2+4-1=controlStop a 0 s+1 := by
      dsimp [k,controlD,controlStop]; push_cast; omega
    simpa only [hp] using hdelim
  · have hp : a+((2*k : Nat):Int)+4+((s+2 : Nat):Int)+2+4=controlBank a 0 s := by
      dsimp [k,controlD,controlBank]; push_cast; omega
    simpa only [hp] using hbank'

#print axioms short_positive_terminal
end Shared.Beeping.NPcoNP.NativeShortCycleTerminal
