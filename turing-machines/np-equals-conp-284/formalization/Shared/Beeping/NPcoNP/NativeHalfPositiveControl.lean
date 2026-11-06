import Shared.Beeping.NPcoNP.NativeHalfPositivePrepared
import Shared.Beeping.NPcoNP.NativeIncBlock
import Shared.Beeping.NPcoNP.NativeIncBank
import Shared.Beeping.NPcoNP.NativeIncSelected
import Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch

/-! Derive the canonical control geometry and selected suffix from the
prepared HALF bank layout. The positive carry remains a separate obligation. -/
namespace Shared.Beeping.NPcoNP.NativeHalfPositiveControl
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping.NPcoNP.NativeHalfSelectedGeneralScan
open Shared.Beeping.NPcoNP.NativeHalfPositivePrepared
open Shared.Beeping.NPcoNP.NativeIncBlock
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem prepared_positive_to1 (state : Fin 185) (path : Path) (name : String) (values : List Nat)
    (leaf : graphLeaf state=some (path,name)) (entry : operationEntry name=some (entryAt values.length))
    (hlen : values.length≤3) (origin h separator : Int) (t : Int → Bool) (m : Nat) (right : List Nat)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+3≤separator)
    (word : Holds t origin path) (leftBlank : ∀ q, q<origin → t q=false)
    (marker : t h=true) (z1 : t (h+1)=false)
    (control : ∀ q, h+2≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ (block (m+1) ++ (encode right ++ [true,false]))))
    (tail : ∀ q, separator+2+((encode values ++ block (m+1) ++ encode right).length : Int)≤q → t q=false) :
    let r := (separator-h-3).toNat
    let left := r::values
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
  let r := (separator-h-3).toNat
  have hr : (r : Int)=separator-h-3 := Int.toNat_of_nonneg (by omega)
  let left := r::values
  let pos := separator+1+((encode values).length : Int)
  have hblock : Holds t (h+2) (block r) := by
    apply holds_ones_delimiter (r+1) (h+2) t
    · intro i hi
      exact control _ (by omega) (by omega)
    · have he : h+2+((r+1 : Nat) : Int)=separator := by push_cast; omega
      change t (h+2+((r+1 : Nat) : Int))=false
      rw [he]
      exact sep
  obtain ⟨hprefix,hselected⟩ := holds_split t (separator+1) (encode values)
    (block (m+1) ++ (encode right ++ [true,false])) bank
  have hfirst : t pos=true ∧ t (pos+1)=true ∧
      Holds t (pos+2) ((List.replicate m true ++ false::encode right) ++ [true,false]) := by
    dsimp [pos]
    have he : separator+1+((encode values).length : Int)+1+1=separator+1+((encode values).length : Int)+2 := by omega
    simpa [block,List.replicate_succ,Nat.add_assoc,Holds,List.append_assoc,he] using hselected
  have hprefix' : Holds t (separator+1) (encode values ++ [true]) := by
    apply holds_append_intro t (separator+1) (encode values) [true] hprefix
    simpa [pos,Holds] using hfirst.1
  have hleft : Holds t (h+2) (leftSuffix left) := by
    have he : h+2+((block r).length : Int)=separator+1 := by simp [block_length]; omega
    have hh := holds_append_intro t (h+2) (block r) (encode values ++ [true]) hblock (by simpa only [he] using hprefix')
    simpa [leftSuffix,left,encode,List.append_assoc] using hh
  have hgeometry : h+2+((leftSuffix left).length : Int)=separator+2+((encode values).length : Int) := by
    simp [leftSuffix,left,encode,block_length,List.length_append,Nat.cast_add]
    omega
  have htail : ∀ q, separator+4+((encode values).length : Int)+
      (((List.replicate m true ++ false::encode right).length : Nat):Int)≤q → t q=false := by
    intro q hq
    apply tail
    simp only [List.length_append,List.length_replicate,List.length_cons,block_length,Nat.cast_add] at *
    push_cast at *
    omega
  exact NativeHalfPositivePrepared.prepared_positive_to1 state path name values leaf entry hlen origin h separator t m left right
    hentry space word leftBlank marker z1 control sep bank hgeometry hleft (by simpa only [pos,show separator+1+((encode values).length : Int)+1=separator+2+((encode values).length : Int) by omega] using hfirst.2.1)
    (by simpa only [pos,show separator+1+((encode values).length : Int)+2=separator+3+((encode values).length : Int) by omega] using hfirst.2.2) htail

#print axioms prepared_positive_to1
end Shared.Beeping.NPcoNP.NativeHalfPositiveControl
