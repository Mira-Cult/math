import Shared.Beeping.NPcoNP.Native279BankScan

/-! The row-9 one-entry scanner crosses the control run and first encoded
bank block, then clears the first bit of the second block. -/
namespace Shared.Beeping.NPcoNP.Native275BankEntry
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.Native279BankScan
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-- A finite control run and two encoded blocks bound the literal scan and
specify the exact whole-tape update. -/
theorem scan_to262 (h separator : Int) (t : Int → Bool) (a b : Nat) (tail : List Bool)
    (hlong : h+11≤separator) (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (ones : ∀ q, h+11≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (block a ++ (block b ++ tail))) :
    let pos := separator+1+((a+2 : Nat) : Int)
    let k := (separator-(h+11)).toNat
    silentSegment machine (cfg 275 (h+9) t) (cfg 262 (pos-2) (clearAt pos t)) (k+a+7) := by
  dsimp only
  let pos := separator+1+((a+2 : Nat) : Int)
  let k := (separator-(h+11)).toNat
  have hk : (k : Int)=separator-(h+11) := Int.toNat_of_nonneg (by omega)
  have hcontrol : ∀ i : Nat, i<k → t (h+11+(i : Int))=true := by
    intro i hi
    apply ones <;> omega
  have hstop : t (h+11+(k : Int))=false := by
    have he : h+11+(k : Int)=separator := by omega
    simpa only [he] using sep
  have s1 := oneSeg machine _ _ (step_zero RightRow.r275 (h+9) t h9)
  have s2 := oneSeg machine _ _ (step_zero RightRow.r271 (h+10) t h10)
  have s1' : silentSegment machine (cfg 275 (h+9) t) (cfg 271 (h+10) t) 1 := by
    simpa only [show h+9+1=h+10 by omega] using s1
  have s2' : silentSegment machine (cfg 271 (h+10) t) (cfg 270 (h+11) t) 1 := by
    simpa only [show h+10+1=h+11 by omega] using s2
  have s12 : silentSegment machine (cfg 275 (h+9) t) (cfg 270 (h+11) t) 2 :=
    segAdd machine _ _ _ 1 1 s1' s2'
  have s3 := scan_run RightRow.r270 k (h+11) t hcontrol hstop
  have s3' : silentSegment machine (cfg 270 (h+11) t) (cfg 9 (separator+1) t) (k+1) := by
    have he : h+11+(k : Int)+1=separator+1 := by omega
    simpa only [he] using s3
  obtain ⟨htail,hdelim,s4⟩ := scan_block RightRow.r9 a (separator+1) t (block b ++ tail) bank
  have htarget : t pos=true := by
    have hh := htail
    change Holds t pos (block b ++ tail) at hh
    simp only [block,List.replicate_succ,List.cons_append,Holds] at hh
    exact hh.1
  have hdelim' : t (pos-1)=false := by
    have he : pos-1=separator+1+((a+1 : Nat):Int) := by dsimp [pos]; omega
    simpa only [he] using hdelim
  have s5 := oneSeg machine _ _ (step42_one pos t htarget)
  have hz : (clearAt pos t) (pos-1)=false := by
    simp [clearAt,show pos-1≠pos by omega,hdelim']
  have s6 := oneSeg machine _ _ (step283_zero (pos-1) (clearAt pos t) hz)
  have s56 : silentSegment machine (cfg 42 pos t) (cfg 262 (pos-2) (clearAt pos t)) 2 := by
    have hs := segAdd machine _ _ _ 1 1 s5 s6
    have he : pos-1-1=pos-2 := by omega
    simpa only [he] using hs
  have s4' : silentSegment machine (cfg 9 (separator+1) t) (cfg 42 pos t) (a+2) := by
    simpa only [pos] using s4
  have pre := segAdd machine _ _ _ 2 (k+1) s12 s3'
  have pre' := segAdd machine _ _ _ (2+(k+1)) (a+2) pre s4'
  have all := segAdd machine _ _ _ (2+(k+1)+(a+2)) 2 pre' s56
  have ht : 2+(k+1)+(a+2)+2=k+a+7 := by omega
  simpa only [ht,pos,k] using all

#print axioms scan_to262
end Shared.Beeping.NPcoNP.Native275BankEntry
