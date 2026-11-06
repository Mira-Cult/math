import Shared.Beeping.NPcoNP.NativeHalfZeroBankScan
import Shared.Beeping.NPcoNP.NativeHalf159Scan

/-! Prepared HALF entries 74--77 scan any supplied prefix of up to three
unary blocks and reach any selected block without changing the bank. -/
namespace Shared.Beeping.NPcoNP.NativeHalfSelectedGeneralScan
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

theorem prepared_to_selected (state : Fin 185) (path : Path) (name : String)
    (values : List Nat) (leaf : graphLeaf state=some (path,name))
    (entry : operationEntry name=some (entryAt values.length)) (hlen : values.length≤3)
    (origin h separator : Int) (t : Int → Bool) (value : Nat) (tail : List Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+3≤separator)
    (word : Holds t origin path) (marker : t h=true) (z1 : t (h+1)=false)
    (control : ∀ q, h+2≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ (block value ++ tail))) :
    let out := clearAt h t
    let pos := separator+1+((encode values).length : Int)
    ∃ steps : Nat, 0<steps ∧ Holds out (separator+1) (encode values ++ (block value ++ tail)) ∧
      out pos=true ∧ (∀ q, q≠h → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 29 pos out) steps := by
  dsimp only
  let out := clearAt h t
  let pos := separator+1+((encode values).length : Int)
  have member := graph_leaf_member state path name leaf
  have walk : PreparedWalk path (.op name) := expanded_leaf_follows traceState557.acc producerExpand (path,name) member
  obtain ⟨_,tailPath⟩ := prepared_head_tail t origin path name walk word
  have hdispatch := expanded_leaf_dispatch_to_entry traceState557.acc producerExpand (path,name) member (entryAt values.length) entry
    (origin+1) t tailPath
  have hlenPath : (path.tail.length : Int)+1=(path.length : Int) := by
    obtain ⟨raw,he,_⟩ := walk
    rw [he]
    simp [preparedPrefix]
  have hdispatch' : silentSegment machine (cfg 93 (origin+1) t) (cfg (entryAt values.length) h t) path.tail.length := by
    have he : origin+1+(path.tail.length : Int)=h := by omega
    simpa only [he] using hdispatch
  have hc : values.length=0 ∨ values.length=1 ∨ values.length=2 ∨ values.length=3 := by omega
  have hrow : machine.table.row (entryAt values.length) true=⟨false,.right,prepareRow values.length,false⟩ := by
    rcases hc with hc | hc | hc | hc <;> simp [hc,entryAt,prepareRow] <;> decide
  have hstep : machine.step (cfg (entryAt values.length) h t)=(cfg (prepareRow values.length) (h+1) out,false) := by
    have hw : (⟨entryAt values.length,h,t⟩ : Config 284).write false=out := rfl
    simp [cfg,Machine.step,marker,hrow,Move.apply,hw]
  have hz1 : out (h+1)=false := by simpa [out,clearAt,show h+1≠h by omega] using z1
  have hstep2 : silentSegment machine (cfg (prepareRow values.length) (h+1) out)
      (cfg (controlRow values.length) (h+2) out) 1 := by
    rcases hc with hc | hc | hc | hc
    · have hh := oneSeg machine _ _ (unchanged_right 45 44 false (h+1) out (by decide) hz1)
      simpa [hc,prepareRow,controlRow,Int.add_assoc] using hh
    · have hh := oneSeg machine _ _ (unchanged_right 46 45 false (h+1) out (by decide) hz1)
      simpa [hc,prepareRow,controlRow,Int.add_assoc] using hh
    · have hh := oneSeg machine _ _ (unchanged_right 47 46 false (h+1) out (by decide) hz1)
      simpa [hc,prepareRow,controlRow,Int.add_assoc] using hh
    · have hh := oneSeg machine _ _ (unchanged_right 48 47 false (h+1) out (by decide) hz1)
      simpa [hc,prepareRow,controlRow,Int.add_assoc] using hh
  let r := (separator-h-2).toNat
  have hr : (r : Int)=separator-h-2 := Int.toNat_of_nonneg (by omega)
  have hones : ∀ i : Nat, i<r → out (h+2+(i : Int))=true := by
    intro i hi
    have hh := control (h+2+(i : Int)) (by omega) (by omega)
    simpa [out,clearAt,show h+2+(i : Int)≠h by omega] using hh
  have hz : out (h+2+(r : Int))=false := by
    have he : h+2+(r : Int)=separator := by omega
    rw [he]
    simpa [out,clearAt,show separator≠h by omega] using sep
  have hscan : silentSegment machine (cfg (controlRow values.length) (h+2) out)
      (cfg (scanRow values.length) (separator+1) out) (r+1) := by
    rcases hc with hc | hc | hc | hc
    · have hh := scan44 r (h+2) out hones hz
      simpa [hc,controlRow,scanRow,show h+2+(r : Int)+1=separator+1 by omega] using hh
    · have hh := scan45 r (h+2) out hones hz
      simpa [hc,controlRow,scanRow,show h+2+(r : Int)+1=separator+1 by omega] using hh
    · have hh := scan46 r (h+2) out hones hz
      simpa [hc,controlRow,scanRow,show h+2+(r : Int)+1=separator+1 by omega] using hh
    · have hh := scan47 r (h+2) out hones hz
      simpa [hc,controlRow,scanRow,show h+2+(r : Int)+1=separator+1 by omega] using hh
  have hbank : Holds out (separator+1) (encode values ++ (block value ++ tail)) := by
    apply holds_transport t out (separator+1) _ bank
    intro p hp _
    simp [out,clearAt,show p≠h by omega]
  obtain ⟨hprefix,hselected⟩ := holds_split out (separator+1) (encode values) (block value ++ tail) hbank
  have hs : out pos=true := by
    dsimp [pos]
    simpa [block,List.replicate_succ,Holds] using hselected.1
  have hbankscan := scan_prefix values (separator+1) out hlen hprefix
  have hbankscan' : silentSegment machine (cfg (scanRow values.length) (separator+1) out)
      (cfg 29 pos out) (encode values).length := by simpa [pos] using hbankscan
  have a := segAdd machine _ _ _ path.tail.length 1 hdispatch' (oneSeg machine _ _ hstep)
  have b := segAdd machine _ _ _ _ 1 a hstep2
  have c := segAdd machine _ _ _ _ (r+1) b hscan
  refine ⟨path.tail.length+1+1+(r+1)+(encode values).length,by omega,hbank,hs,?_,
    segAdd machine _ _ _ _ _ c hbankscan'⟩
  intro p hp
  simp [clearAt,hp]

#print axioms prepared_to_selected_zero
end Shared.Beeping.NPcoNP.NativeHalfSelectedGeneralScan
