import Shared.Beeping.NPcoNP.NativeHalfSelectedGeneralScan
import Shared.Beeping.NPcoNP.NativeHalfSelectedReconstruction

/-! A prepared native HALF parser reaches the positive-value state-1 bank
result, under explicit canonical control, reserve and blank-tail hypotheses.
The following carry and graph successor remain separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeHalfPositivePrepared
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeHalfSelectedGeneralScan
open Shared.Beeping.NPcoNP.NativeHalfSelectedReconstruction
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem prepared_positive_to1 (state : Fin 185) (path : Path) (name : String) (values : List Nat)
    (leaf : graphLeaf state=some (path,name)) (entry : operationEntry name=some (entryAt values.length))
    (hlen : values.length≤3) (origin h separator : Int) (t : Int → Bool) (m : Nat) (left right : List Nat)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+3≤separator)
    (word : Holds t origin path) (leftBlank : ∀ q, q<origin → t q=false)
    (marker : t h=true) (z1 : t (h+1)=false)
    (control : ∀ q, h+2≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ (block (m+1) ++ (encode right ++ [true,false]))))
    (geometry : h+2+((leftSuffix left).length : Int)=separator+2+((encode values).length : Int))
    (leftWord : Holds t (h+2) (leftSuffix left))
    (head : t (separator+2+((encode values).length : Int))=true)
    (suffix : Holds t (separator+3+((encode values).length : Int))
      ((List.replicate m true ++ false::encode right) ++ [true,false]))
    (tail : ∀ q, separator+4+((encode values).length : Int)+
      (((List.replicate m true ++ false::encode right).length : Nat):Int)≤q → t q=false) :
    let result := left ++ [(m+1)/2] ++ right ++ List.replicate ((m+2)/2) 0
    ∃ (steps : Nat) (headPos : Int) (out : Int → Bool), 0<steps ∧
      ((m+1)%2=1 → headPos=h-1) ∧ ((m+1)%2=0 → headPos≤h-2) ∧
      ((m+1)%2=0 → t (headPos+1)=false) ∧
      ((m+1)%2=0 → ∀ p, headPos+1<p → p<h → t p=true) ∧
      ((m+1)%2=0 → ∀ p, headPos+2≤p → p<h → out p=false) ∧
      ((m+1)%2=1 → ∀ p<h, out p=t p) ∧
      ((m+1)%2=0 → ∀ p≤headPos+1, out p=t p) ∧
      out (headPos+1)=false ∧ out h=false ∧ out (h+1)=false ∧
      Holds out (h+2) (encode result) ∧
      out (h+2+((encode result).length : Int))=true ∧
      out (h+3+((encode result).length : Int))=false ∧
      (∀ p, h+3+((encode result).length : Int)≤p → out p=false) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 1 headPos out) steps := by
  dsimp only
  let mid := clearAt h t
  let pos := separator+1+((encode values).length : Int)
  obtain ⟨a,ha,_,hselected,hframe,hscan⟩ :=
    prepared_to_selected state path name values leaf entry hlen origin h separator t (m+1)
      (encode right ++ [true,false]) hentry space word marker z1 control sep bank
  change ∀ q, q≠h → mid q=t q at hframe
  have mh : mid h=false := by simp [mid,clearAt]
  have mz : mid (h+1)=false := (hframe _ (by omega)).trans z1
  have ml : Holds mid (h+2) (leftSuffix left) := by
    apply holds_transport t mid (h+2) _ leftWord
    intro p hp _
    exact (hframe p (by omega)).symm
  have mhead : mid (h+2+((leftSuffix left).length : Int))=true := by
    rw [geometry,hframe _ (by omega)]
    exact head
  have mselected : mid (h+2+((leftSuffix left).length : Int)-1)=true := by
    have he : h+2+((leftSuffix left).length : Int)-1=pos := by dsimp [pos]; omega
    simpa [he] using hselected
  have mleft : ∀ q, q≤origin-1 → mid q=false := by
    intro q hq
    rw [hframe q (by omega)]
    exact leftBlank q (by omega)
  have mword : Holds mid (h+2+((leftSuffix left).length : Int)+1)
      ((List.replicate m true ++ false::encode right) ++ [true,false]) := by
    rw [geometry,show separator+2+((encode values).length : Int)+1=separator+3+((encode values).length : Int) by omega]
    apply holds_transport t mid _ _ suffix
    intro p hp _
    exact (hframe p (by omega)).symm
  have mtail : ∀ q, h+2+((leftSuffix left).length : Int)+2+
      (((List.replicate m true ++ false::encode right).length : Nat):Int)≤q → mid q=false := by
    intro q hq
    rw [hframe q (by omega)]
    apply tail
    rw [geometry] at hq
    omega
  obtain ⟨b,headPos,out,hb,hodd,heven,hstop,hones,hclear,hoddframe,hevenframe,hzero,hctrl,hctrl1,hbank,hmark,hblank,htail,hsegment⟩ :=
    positive_selected_of_word mid h (origin-1) left right m mh mz ml mhead mselected mleft (by omega) mword mtail
  have hscan' : silentSegment machine (cfg 93 (origin+1) t)
      (cfg 29 (h+2+((leftSuffix left).length : Int)-1) mid) a := by
    have he : h+2+((leftSuffix left).length : Int)-1=pos := by dsimp [pos]; omega
    simpa [he] using hscan
  refine ⟨a+b,headPos,out,by omega,hodd,heven,?_,?_,hclear,?_,?_,hzero,hctrl,hctrl1,hbank,hmark,hblank,htail,
    segAdd machine _ _ _ a b hscan' hsegment⟩
  · intro he; rw [←hframe _ (by have hh := heven he; omega)]; exact hstop he
  · intro he p hp hp'; rw [←hframe p (by omega)]; exact hones he p hp hp'
  · intro ho p hp; rw [hoddframe ho p hp,hframe p (by omega)]
  · intro he p hp; rw [hevenframe he p hp,hframe p (by have hh := heven he; omega)]

#print axioms prepared_positive_to1
end Shared.Beeping.NPcoNP.NativeHalfPositivePrepared
