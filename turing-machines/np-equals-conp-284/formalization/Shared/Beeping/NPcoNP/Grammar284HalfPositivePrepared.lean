import Shared.Beeping.NPcoNP.Grammar284HalfPositiveSuccessor
import Shared.Beeping.NPcoNP.NativeHalfPositiveControl
import Shared.Beeping.NPcoNP.NativeIncBank
import Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
import Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

/-! A prepared positive-valued native HALF executes its bank calculation and carry
to the first expanded successor, under an explicit reserve and blank tail. -/
namespace Shared.Beeping.NPcoNP.Grammar284HalfPositivePrepared
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping.NPcoNP.NativeHalfSelectedGeneralScan
open Shared.Beeping.NPcoNP.NativeHalfPositiveControl
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284SuccessorShapeBase
open Shared.Beeping.NPcoNP.Grammar284SuccessorShape
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284HalfPositiveSuccessor
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 30000000

theorem prepared_positive_to_first_successor (row : Fin 185) (dst : Nat) (path : Path) (name : String)
    (values right : List Nat) (m skip : Nat) (hskip : skip≤1)
    (leaf : graphLeaf row=some (path,name)) (entry : operationEntry name=some (entryAt values.length))
    (hlen : values.length≤3)
    (parity : (skip=0 ∧ (m+1)%2=1) ∨ (skip=1 ∧ (m+1)%2=0))
    (hshape : successorShape path skip=true) (hrightmost : rightmostOK path skip=true)
    (hlast : path.getLast?=some false) (hsucc : successor traceState557.acc.starts path skip=some dst)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (leftBlank : ∀ q, q<origin → t q=false) (marker : t h=true) (z1 : t (h+1)=false)
    (control : ∀ q, h+2≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ (block (m+1) ++ (encode right ++ [true,false]))))
    (tail : ∀ q, separator+2+((encode values ++ block (m+1) ++ encode right).length : Int)≤q → t q=false) :
    let result := values ++ [(m+1)/2] ++ right ++ List.replicate ((m+2)/2) 0
    ∃ (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧ 0<steps ∧ Holds out origin next ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out separator=false ∧ out (separator-1)=true ∧
      Holds out (separator+1) (encode result ++ [true,false]) ∧
      (∀ q, separator+2+((encode result).length : Int)≤q → out q=false) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  let r := (separator-h-3).toNat
  have hr : (r : Int)=separator-h-3 := Int.toNat_of_nonneg (by omega)
  let result := values ++ [(m+1)/2] ++ right ++ List.replicate ((m+2)/2) 0
  let full := (r::values) ++ [(m+1)/2] ++ right ++ List.replicate ((m+2)/2) 0
  obtain ⟨a,head,mid,ha,hodd,heven,hstop,honesOrig,_,hoddframe,hevenframe,hz,hzero,hz1,hfull,hreserve,hblank,hblankTail,hsegment⟩ :=
    NativeHalfPositiveControl.prepared_positive_to1 row path name values leaf entry hlen origin h separator t m right
      hentry (by omega) word leftBlank marker z1 control sep bank tail
  have hlastword : path.dropLast ++ [false]=path :=
    List.dropLast_append_getLast? false (by simp [hlast])
  have hlastlen : path.dropLast.length+1=path.length := by
    have hh := congrArg List.length hlastword
    simpa using hh
  have hlastHold : Holds t origin (path.dropLast ++ [false]) := by rw [hlastword]; exact word
  obtain ⟨_,hlastTail⟩ := Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch.holds_split t origin path.dropLast [false] hlastHold
  have lastZero : t (h-1)=false := by
    have hh : t (origin+(path.dropLast.length : Int))=false := by simpa [Holds] using hlastTail
    have he : origin+(path.dropLast.length : Int)=h-1 := by omega
    simpa only [he] using hh
  have hhead : head=h-1-(skip : Int) := by
    rcases parity with ⟨hs,ho⟩ | ⟨hs,he⟩
    · rw [hs]; simp; exact hodd ho
    · have hh := heven he
      have hone := honesOrig he
      have heq : head=h-2 := by
        by_contra hn
        have ht : t (h-1)=true := hone (h-1) (by omega) (by omega)
        rw [lastZero] at ht
        contradiction
      rw [hs,heq]; norm_num; omega
  have hframe : ∀ q, q<h → mid q=t q := by
    intro q hq
    rcases parity with ⟨hs,ho⟩ | ⟨hs,he⟩
    · exact hoddframe ho q hq
    · apply hevenframe he
      rw [hs] at hhead
      norm_num at hhead
      omega
  have hreturn : silentSegment machine (cfg 93 (origin+1) t) (cfg 1 (h-1-(skip : Int)) mid) a := by simpa [hhead] using hsegment
  have hfull' : Holds mid (h+2) (block r ++ encode result) := by
    simpa [full,result,encode,List.append_assoc] using hfull
  obtain ⟨hblock,hresult⟩ := holds_split mid (h+2) (block r) (encode result) hfull'
  have hresult' : Holds mid (separator+1) (encode result) := by
    have he : h+2+((block r).length : Int)=separator+1 := by simp [block_length]; omega
    simpa only [he] using hresult
  have mark : mid (h+2)=true := by
    have hh := holds_get mid (h+2) (block r) hblock 0 (by simp [block])
    simpa [block] using hh
  have ones : ∀ q, h+2<q → q<separator → mid q=true := by
    intro q hq hq'
    let i := (q-(h+2)).toNat
    have hi : (i : Int)=q-(h+2) := Int.toNat_of_nonneg (by omega)
    have hib : i<r+1 := by omega
    have hh := holds_get mid (h+2) (block r) hblock i (by simp [block]; omega)
    have hi' : i<(List.replicate (r+1) true).length := by simpa using hib
    have he : h+2+(i : Int)=q := by omega
    rw [he] at hh
    simpa only [block,List.getElem_append_left hi',List.getElem_replicate] using hh
  have sep' : mid separator=false := by
    have hh := holds_get mid (h+2) (block r) hblock (r+1) (by simp [block])
    have he : h+2+((r+1 : Nat) : Int)=separator := by push_cast; omega
    rw [he] at hh
    simpa [block] using hh
  have hend : h+2+((encode full).length : Int)=separator+1+((encode result).length : Int) := by
    simp [full,result,encode,block_length,List.length_append,Nat.cast_add]
    omega
  have hreserve' : mid (separator+1+((encode result).length : Int))=true := by simpa [←hend,full] using hreserve
  have hblank' : mid (separator+2+((encode result).length : Int))=false := by
    have he : h+3+((encode full).length : Int)=separator+2+((encode result).length : Int) := by omega
    simpa [←he,full] using hblank
  have hbankword : Holds mid (separator+1) (encode result ++ [true,false]) := by
    apply holds_append_intro mid (separator+1) (encode result) [true,false] hresult'
    simp [Holds,hreserve',show separator+1+((encode result).length : Int)+1=separator+2+((encode result).length : Int) by omega,hblank']
  have hbt : ∀ q, h+3+((encode full).length : Int)≤q → mid q=false := by
    simpa [full,result,r,Nat.add_assoc] using hblankTail
  have hright : ∀ q, separator+2+((encode result).length : Int)≤q → mid q=false := by
    intro q hq
    apply hbt
    have he : h+3+((encode full).length : Int)=separator+2+((encode result).length : Int) := by omega
    rw [he]
    exact hq
  apply Shared.Beeping.NPcoNP.Grammar284HalfPositiveSuccessor.prepared_positive_to_first_successor row dst path name skip hskip leaf hshape hrightmost hlast hsucc
    origin h separator (separator+2+((encode result).length : Int)) t (encode result ++ [true,false])
    hentry space room word leftBlank (by omega)
  exact ⟨a,mid,ha,hframe,hzero,hz1,mark,ones,sep',hbankword,hright,hreturn⟩

#print axioms prepared_positive_to_first_successor
end Shared.Beeping.NPcoNP.Grammar284HalfPositivePrepared
