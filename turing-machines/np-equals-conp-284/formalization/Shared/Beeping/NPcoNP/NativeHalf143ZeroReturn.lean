import Shared.Beeping.NPcoNP.NativeHalf143Scan
import Shared.Beeping.NPcoNP.NativeHalfOddReturn
import Shared.Beeping.NPcoNP.NativeHalfOddFinish

/-! The zero selected at the row-143 HALF entry returns to the state-1 carry
without changing the bank. The subsequent grammar successor is separate. -/
namespace Shared.Beeping.NPcoNP.NativeHalf143ZeroReturn
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalf143Scan
open Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
open Shared.Beeping.NPcoNP.NativeHalfEntryZero
open Shared.Beeping.NPcoNP.NativeHalfOddReturn
open Shared.Beeping.NPcoNP.NativeHalfOddFinish
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000

theorem scan25_ones (n : Nat) (h : Int) (t : Int → Bool)
    (ones : ∀ i : Nat, i<n → t (h-(i : Int))=true)
    (z0 : t (h-(n : Int))=false) (z1 : t (h-(n : Int)-1)=false) :
    silentSegment machine (cfg 25 h t) (cfg 95 (h-(n : Int)-2) t) (n+2) := by
  induction n generalizing h with
  | zero =>
    have a := oneSeg machine _ _ (step25_zero h t (by simpa using z0))
    have b := oneSeg machine _ _ (step26_zero (h-1) t (by simpa using z1))
    have all := segAdd machine _ _ _ 1 1 a b
    simpa only [Nat.cast_zero,Int.sub_zero,show h-1-1=h-2 by omega] using all
  | succ n ih =>
    have hfirst : t h=true := by simpa using ones 0 (by omega)
    have hrest : ∀ i : Nat, i<n → t ((h-1)-(i : Int))=true := by
      intro i hi
      have hh := ones (i+1) (by omega)
      simpa [Nat.cast_add,Int.sub_sub,Int.add_comm,Int.add_left_comm,Int.add_assoc] using hh
    have hz0 : t ((h-1)-(n : Int))=false := by
      simpa [Nat.cast_add,Int.sub_sub,Int.add_comm,Int.add_left_comm,Int.add_assoc] using z0
    have hz1 : t ((h-1)-(n : Int)-1)=false := by
      simpa [Nat.cast_add,Int.sub_sub,Int.add_comm,Int.add_left_comm,Int.add_assoc] using z1
    have a := oneSeg machine _ _ (step25_one h t hfirst)
    have b := ih (h-1) hrest hz0 hz1
    have all := segAdd machine _ _ _ 1 (n+2) a b
    have he : (h-1)-(n : Int)-2=h-((n+1 : Nat) : Int)-2 := by push_cast; omega
    simpa only [he,show 1+(n+2)=(n+1)+2 by omega] using all

theorem prepared_zero_to1 (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (entry : operationEntry name=some 75)
    (origin h separator : Int) (t : Int → Bool) (tail : List Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+3≤separator)
    (word : Holds t origin path) (marker : t h=true) (lastZero : t (h-1)=false)
    (z1 : t (h+1)=false) (control : ∀ q, h+2≤q → q<separator → t q=true)
    (sep : t separator=false) (bank : Holds t (separator+1) ([true,false,true,false,true,false] ++ tail)) :
    let out := clearAt h t
    ∃ steps : Nat, 0<steps ∧ Holds out (separator+1) ([true,false,true,false,true,false] ++ tail) ∧
      (∀ q, q≠h → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 1 (h-2) out) steps := by
  dsimp only
  let out := clearAt h t
  obtain ⟨a,ha,hbank,hsel,hselzero,hframe,hscan⟩ :=
    prepared_to_selected_zero state path name leaf entry origin h separator t tail hentry space word marker z1 control sep bank
  change ∀ q, q≠h → out q=t q at hframe
  have hb := hbank
  simp only [List.cons_append,Holds] at hb
  obtain ⟨b0,b1,b2,b3,b4,b5,_⟩ := hb
  have b0' : out (separator+1)=true := b0
  have b1' : out (separator+2)=false := by simpa only [show separator+1+1=separator+2 by omega] using b1
  have b2' : out (separator+3)=true := by simpa only [show separator+1+1+1=separator+3 by omega] using b2
  have b3' : out (separator+4)=false := by simpa only [show separator+1+1+1+1=separator+4 by omega] using b3
  have hsep : out separator=false := (hframe separator (by omega)).trans sep
  have hlastControl : out (separator-1)=true := by
    rw [hframe (separator-1) (by omega)]
    exact control _ (by omega) (by omega)
  have hz0 : out h=false := by simp [out,clearAt]
  have hz1 : out (h+1)=false := (hframe _ (by omega)).trans z1
  have hlast : out (h-1)=false := (hframe _ (by omega)).trans lastZero
  have s0 := oneSeg machine _ _ (step29_one (separator+5) out hsel)
  have s1 := oneSeg machine _ _ (step41_zero (separator+6) out hselzero)
  have s01 : silentSegment machine (cfg 29 (separator+5) out) (cfg 25 (separator+5) out) 2 := by
    have h0 : separator+5+1=separator+6 := by omega
    have h1 : separator+6-1=separator+5 := by omega
    rw [h0] at s0
    rw [h1] at s1
    exact segAdd machine _ _ _ 1 1 s0 s1
  have a0 := oneSeg machine _ _ (step25_one (separator+5) out hsel)
  have a1 := oneSeg machine _ _ (step25_zero (separator+4) out b3')
  have a2 := oneSeg machine _ _ (step26_one (separator+3) out b2')
  have a3 := oneSeg machine _ _ (step25_zero (separator+2) out b1')
  have a4 := oneSeg machine _ _ (step26_one (separator+1) out b0')
  have a5 := oneSeg machine _ _ (step25_zero separator out hsep)
  have a6 := oneSeg machine _ _ (step26_one (separator-1) out hlastControl)
  have pre : silentSegment machine (cfg 25 (separator+5) out) (cfg 25 (separator-2) out) 7 := by
    have t0 : silentSegment machine (cfg 25 (separator+5) out) (cfg 25 (separator+4) out) 1 := by simpa only [show separator+5-1=separator+4 by omega] using a0
    have t1 : silentSegment machine (cfg 25 (separator+4) out) (cfg 26 (separator+3) out) 1 := by simpa only [show separator+4-1=separator+3 by omega] using a1
    have t2 : silentSegment machine (cfg 26 (separator+3) out) (cfg 25 (separator+2) out) 1 := by simpa only [show separator+3-1=separator+2 by omega] using a2
    have t3 : silentSegment machine (cfg 25 (separator+2) out) (cfg 26 (separator+1) out) 1 := by simpa only [show separator+2-1=separator+1 by omega] using a3
    have t4 : silentSegment machine (cfg 26 (separator+1) out) (cfg 25 separator out) 1 := by simpa only [show separator+1-1=separator by omega] using a4
    have t5 : silentSegment machine (cfg 25 separator out) (cfg 26 (separator-1) out) 1 := a5
    have t6 : silentSegment machine (cfg 26 (separator-1) out) (cfg 25 (separator-2) out) 1 := by simpa only [show separator-1-1=separator-2 by omega] using a6
    exact segAdd machine _ _ _ 6 1
      (segAdd machine _ _ _ 5 1 (segAdd machine _ _ _ 4 1 (segAdd machine _ _ _ 3 1
        (segAdd machine _ _ _ 2 1 (segAdd machine _ _ _ 1 1 t0 t1) t2) t3) t4) t5) t6
  let r := (separator-h-3).toNat
  have hr : (r : Int)=separator-h-3 := Int.toNat_of_nonneg (by omega)
  have hones : ∀ i : Nat, i<r → out ((separator-2)-(i : Int))=true := by
    intro i hi
    rw [hframe _ (by omega)]
    exact control _ (by omega) (by omega)
  have hcontrolEnd : (separator-2)-(r : Int)=h+1 := by omega
  have hzfirst : out ((separator-2)-(r : Int))=false := by rw [hcontrolEnd]; exact hz1
  have hzsecond : out ((separator-2)-(r : Int)-1)=false := by rw [hcontrolEnd,show h+1-1=h by omega]; exact hz0
  have hback := scan25_ones r (separator-2) out hones hzfirst hzsecond
  have hback' : silentSegment machine (cfg 25 (separator-2) out) (cfg 95 (h-1) out) (r+2) := by
    have he : separator-2-(r : Int)-2=h-1 := by omega
    simpa only [he] using hback
  have hend := oneSeg machine _ _ (step95_zero (h-1) out hlast)
  have hend' : silentSegment machine (cfg 95 (h-1) out) (cfg 1 (h-2) out) 1 := by
    simpa only [show h-1-1=h-2 by omega] using hend
  have chain := segAdd machine _ _ _ a 2 hscan s01
  have chain' := segAdd machine _ _ _ _ 7 chain pre
  have chain'' := segAdd machine _ _ _ _ (r+2) chain' hback'
  exact ⟨a+2+7+(r+2)+1,by omega,hbank,hframe,segAdd machine _ _ _ _ 1 chain'' hend'⟩

#print axioms prepared_zero_to1
end Shared.Beeping.NPcoNP.NativeHalf143ZeroReturn
