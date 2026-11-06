import Shared.Beeping.NPcoNP.NativeHalfSelectedGeneralScan
import Shared.Beeping.NPcoNP.NativeHalfZeroBankScan
import Shared.Beeping.NPcoNP.NativeHalf159Scan

/-! Prepared HALF entries 74--77 scan any supplied prefix of up to three
unary blocks and reach the selected zero block without changing the bank. -/
namespace Shared.Beeping.NPcoNP.NativeHalfZeroGeneralScan
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeRightDispatchGeneric
open Shared.Beeping.NPcoNP.NativeFirstNextPath
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
open Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping.NPcoNP.NativeRow13Scan
open Shared.Beeping.NPcoNP.NativeHalf143Scan
open Shared.Beeping.NPcoNP.NativeHalf159Scan
open Shared.Beeping.NPcoNP.NativeHalfZeroBankScan
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

def entryAt : Nat → Fin 284 | 0 => 77 | 1 => 74 | 2 => 75 | _ => 76
def prepareRow : Nat → Fin 284 | 0 => 45 | 1 => 46 | 2 => 47 | _ => 48
def controlRow : Nat → Fin 284 | 0 => 44 | 1 => 45 | 2 => 46 | _ => 47

theorem prepared_to_selected_zero (state : Fin 185) (path : Path) (name : String)
    (values : List Nat) (leaf : graphLeaf state=some (path,name))
    (entry : operationEntry name=some (entryAt values.length)) (hlen : values.length≤3)
    (origin h separator : Int) (t : Int → Bool) (tail : List Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+3≤separator)
    (word : Holds t origin path) (marker : t h=true) (z1 : t (h+1)=false)
    (control : ∀ q, h+2≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ ([true,false] ++ tail))) :
    let out := clearAt h t
    let pos := separator+1+((encode values).length : Int)
    ∃ steps : Nat, 0<steps ∧ Holds out (separator+1) (encode values ++ ([true,false] ++ tail)) ∧
      out pos=true ∧ out (pos+1)=false ∧ (∀ q, q≠h → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 29 pos out) steps := by
  have entry' : operationEntry name=some (Shared.Beeping.NPcoNP.NativeHalfSelectedGeneralScan.entryAt values.length) := by
    exact entry
  obtain ⟨steps,hsteps,hbank,hfirst,hframe,hsegment⟩ :=
    Shared.Beeping.NPcoNP.NativeHalfSelectedGeneralScan.prepared_to_selected state path name values leaf entry' hlen
      origin h separator t 0 tail hentry space word marker z1 control sep (by simpa [block] using bank)
  have hbank' : Holds (clearAt h t) (separator+1) (encode values ++ ([true,false] ++ tail)) := by
    simpa [block] using hbank
  obtain ⟨_,hselected⟩ := holds_split (clearAt h t) (separator+1) (encode values) ([true,false] ++ tail) hbank'
  have hsecond : (clearAt h t) (separator+1+((encode values).length : Int)+1)=false := by
    simp only [List.cons_append,Holds] at hselected
    exact hselected.2.1
  exact ⟨steps,hsteps,hbank',hfirst,hsecond,hframe,hsegment⟩

#print axioms prepared_to_selected_zero
end Shared.Beeping.NPcoNP.NativeHalfZeroGeneralScan
