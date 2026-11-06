import Shared.Beeping.NPcoNP.Native279BankScan

/-! Literal state-271 scan of the control run and first bank block. -/
namespace Shared.Beeping.NPcoNP.Native271BankScan
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Native279BankScan
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-- Two zeros and a finite one-run lead to the first encoded bank value.
The machine clears its first cell and returns silently to state 262. -/
theorem scan271_to262 (h : Int) (t : Int → Bool) (k value : Nat) (tail : List Bool)
    (h0 : t h=false) (h1 : t (h+1)=false)
    (control : ∀ i : Nat, i<k → t (h+2+(i : Int))=true)
    (delimiter : t (h+2+(k : Int))=false)
    (bank : Holds t (h+3+(k : Int)) (block value ++ tail)) :
    let pos := h+3+(k : Int)
    (∀ q, q≠pos → clearAt pos t q=t q) ∧
    silentSegment machine (cfg 271 h t) (cfg 262 (pos-2) (clearAt pos t)) (k+5) := by
  dsimp only
  let pos := h+3+(k : Int)
  have ha := oneSeg machine _ _ (step_zero RightRow.r271 h t h0)
  have hb := oneSeg machine _ _ (step_zero RightRow.r270 (h+1) t h1)
  have hab : silentSegment machine (cfg 271 h t) (cfg 9 (h+2) t) 2 := by
    have hs := segAdd machine _ _ _ 1 1 ha hb
    simpa [Int.add_assoc] using hs
  have hc := scan_run RightRow.r9 k (h+2) t control delimiter
  have hc' : silentSegment machine (cfg 9 (h+2) t) (cfg 42 pos t) (k+1) := by
    have he : h+2+(k : Int)+1=pos := by dsimp [pos]; omega
    simpa only [he] using hc
  have htarget : t pos=true := by
    change Holds t pos (block value ++ tail) at bank
    simp only [block,List.replicate_succ,List.cons_append,Holds] at bank
    exact bank.1
  have hzero : t (pos-1)=false := by
    have he : pos-1=h+2+(k : Int) := by dsimp [pos]; omega
    simpa only [he] using delimiter
  let u := clearAt pos t
  have hz' : u (pos-1)=false := by simp [u,clearAt,show pos-1≠pos by omega,hzero]
  have hs1 := oneSeg machine _ _ (step42_one pos t htarget)
  have hs2 := oneSeg machine _ _ (step283_zero (pos-1) u hz')
  have hlast : silentSegment machine (cfg 42 pos t) (cfg 262 (pos-2) u) 2 := by
    have hs := segAdd machine _ _ _ 1 1 hs1 hs2
    have he : pos-1-1=pos-2 := by omega
    simpa [u,he] using hs
  have hpre := segAdd machine _ _ _ 2 (k+1) hab hc'
  have hall := segAdd machine _ _ _ (2+(k+1)) 2 hpre hlast
  constructor
  · intro q hq
    simp [clearAt,hq]
  · have he : 2+(k+1)+2=k+5 := by omega
    simpa only [he,pos,u] using hall

#print axioms scan271_to262
end Shared.Beeping.NPcoNP.Native271BankScan
