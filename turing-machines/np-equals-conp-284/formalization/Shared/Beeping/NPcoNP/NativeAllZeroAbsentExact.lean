import Shared.Beeping.NPcoNP.NativeAllZeroAbsentReturn
import Shared.Beeping.NPcoNP.NativeHalfScannerReturns

/-! Exact state-261 return after the marker-absent selector cycle.
This prepared-layout analysis is not a blank-start or graph-refinement result. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroAbsentExact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerReturns
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentReturn
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

/-- From state 261, a supplied zero run and its following one determine the
exact output tape, head and silent time. -/
theorem dispatch261_return83_exact (k : Nat) (h : Int) (t : Int → Bool)
    (hk : 0<k) (h0 : t h=false) (h1 : t (h+1)=false)
    (hz : ∀ i : Nat, i<k → t (h+2+(i : Int))=false)
    (hm : t (h+2+(k : Int))=true) :
    silentSegment machine (cfg 261 h t)
      (cfg 83 (h+(k : Int)) (fillRange (setAt h t) (h+2) (h+2+(k : Int)))) (k+4) := by
  let t1 := setAt h t
  have h1' : t1 (h+1)=false := by simp [t1,setAt,h1,show h+1≠h by omega]
  have hz' : ∀ i : Nat, i<k → t1 (h+2+(i : Int))=false := by
    intro i hi
    change (if h+2+(i : Int)=h then true else t (h+2+(i : Int)))=false
    rw [if_neg (by omega)]
    exact hz i hi
  have hm' : t1 (h+2+(k : Int))=true := by
    change (if h+2+(k : Int)=h then true else t (h+2+(k : Int)))=true
    rw [if_neg (by omega)]
    exact hm
  have hfirst := oneSeg machine _ _ (step261_zero h t h0)
  have hsecond := oneSeg machine _ _ (step42_zero (h+1) t1 h1')
  have hprefix : silentSegment machine (cfg 261 h t) (cfg 10 (h+2) t1) 2 := by
    have hseg := segAdd machine _ _ _ 1 1 hfirst hsecond
    have he : h+1+1=h+2 := by omega
    simpa only [he] using hseg
  have hscan := scan10_return83 k (h+2) t1 hk hz' hm'
  have hall := segAdd machine _ _ _ 2 (k+2) hprefix hscan
  have hp : h+2+(k : Int)-2=h+(k : Int) := by omega
  have hn : 2+(k+2)=k+4 := by omega
  simpa only [hp,hn,t1] using hall

/-- The right-hand scan corridor is cleared strictly before the marker. -/
theorem return_right_gap (d : Int) (r : Nat) (t : Int → Bool) (q : Int)
    (lo : d+2≤q) (hi : q<d+1+(r : Int)) : outTape d r t q=false := by
  unfold outTape
  rw [put_other _ _ _ _ (by omega)]
  change (if d+3≤q ∧ q<d+2+(r : Int) then false else scanTape d t q)=false
  by_cases he : q=d+2
  · rw [he]
    simp [scanTape,put]
  · rw [if_pos (by omega)]

def intermediate (a : Int) (r v : Nat) (rest : List Nat) (t : Int → Bool) : Int → Bool :=
  outTape (a+30) (r+3) (selectorOutput a r v rest t)

/-- The exact return has two possible forms, depending only on the one cell
not determined by the return tape's local specification. -/
theorem absent_return_exact (a : Int) (r v : Nat) (rest : List Nat) (t : Int → Bool) :
    let final := intermediate a r v rest t
    (final (a+31)=true →
      silentSegment machine (cfg 261 (a+28) final)
        (cfg 83 (a+29) (fillRange (setAt (a+28) final) (a+30) (a+31))) 5) ∧
    (final (a+31)=false →
      silentSegment machine (cfg 261 (a+28) final)
        (cfg 83 (a+32+(r : Int))
          (fillRange (setAt (a+28) final) (a+30) (a+34+(r : Int)))) (r+8)) := by
  dsimp only
  let final := intermediate a r v rest t
  have h0 : final (a+28)=false := by
    apply return_carry_gap
    all_goals omega
  have h1 : final (a+28+1)=false := by
    apply return_carry_gap
    all_goals omega
  have h2 : final (a+30)=false := by
    dsimp [final,intermediate]
    rw [return_at_start]
    unfold selectorOutput
    rw [spec_outside _ _ _ _ (Or.inl (by push_cast; omega))]
    simp [clearAt]
  constructor
  · intro hb
    have hz : ∀ i : Nat, i<1 → final (a+28+2+(i : Int))=false := by
      intro i hi
      have hi0 : i=0 := by omega
      subst i
      have he : a+28+2+((0 : Nat):Int)=a+30 := by omega
      simpa only [he] using h2
    have hm : final (a+28+2+((1 : Nat):Int))=true := by
      have he : a+28+2+((1 : Nat):Int)=a+31 := by omega
      simpa only [he] using hb
    have h := dispatch261_return83_exact 1 (a+28) final (by omega) h0 h1 hz hm
    have hstart : a+28+2=a+30 := by omega
    have hend : a+28+2+((1 : Nat):Int)=a+31 := by omega
    have hhead : a+28+((1 : Nat):Int)=a+29 := by omega
    have hend2 : a+30+((1 : Nat):Int)=a+31 := by omega
    simpa only [hstart,hend,hend2,hhead, show 1+4=5 by decide] using h
  · intro hb
    have hz : ∀ i : Nat, i<r+4 → final (a+28+2+(i : Int))=false := by
      intro i hi
      by_cases hi0 : i=0
      · subst i
        have he : a+28+2+((0 : Nat):Int)=a+30 := by omega
        simpa only [he] using h2
      · by_cases hi1 : i=1
        · subst i
          have he : a+28+2+((1 : Nat):Int)=a+31 := by omega
          simpa only [he] using hb
        · change outTape (a+30) (r+3) (selectorOutput a r v rest t) (a+28+2+(i : Int))=false
          apply return_right_gap
          · omega
          · push_cast at *
            omega
    have hm : final (a+28+2+((r+4 : Nat):Int))=true := by
      change outTape (a+30) (r+3) (selectorOutput a r v rest t) (a+28+2+((r+4 : Nat):Int))=true
      have he : a+28+2+((r+4 : Nat):Int)=a+30+1+((r+3 : Nat):Int) := by push_cast; omega
      rw [he]
      exact return_marker _ _ _
    have h := dispatch261_return83_exact (r+4) (a+28) final (by omega) h0 h1 hz hm
    have hstart : a+28+2=a+30 := by omega
    have hend : a+28+2+((r+4 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
    have hhead : a+28+((r+4 : Nat):Int)=a+32+(r : Int) := by push_cast; omega
    have htime : r+4+4=r+8 := by omega
    have hend2 : a+30+((r+4 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
    simpa only [hstart,hend,hend2,hhead,htime] using h

/-- Either exact return preserves the entire tape left of the state-261
head and at or to the right of the later marker. -/
theorem absent_return_frames (a : Int) (r v : Nat) (rest : List Nat) (t : Int → Bool)
    (q : Int) (hq : q<a+28 ∨ a+34+(r : Int)≤q) :
    let final := intermediate a r v rest t
    fillRange (setAt (a+28) final) (a+30) (a+31) q=final q ∧
    fillRange (setAt (a+28) final) (a+30) (a+34+(r : Int)) q=final q := by
  have hs : q≠a+28 := by omega
  have hshort : ¬ (a+30≤q ∧ q<a+31) := by omega
  have hlong : ¬ (a+30≤q ∧ q<a+34+(r : Int)) := by omega
  simp [fillRange,setAt,hs,hshort,hlong]

#print axioms absent_return_frames
#print axioms return_right_gap
#print axioms absent_return_exact
#print axioms dispatch261_return83_exact
end Shared.Beeping.NPcoNP.NativeAllZeroAbsentExact
