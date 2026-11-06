import Shared.Beeping.NPcoNP.NativeHalf143Scan
import Shared.Beeping.NPcoNP.Grammar284HalfPreparation
import Shared.Beeping.NPcoNP.NativeRow13Scan
import Shared.Beeping.NPcoNP.NativeHalfEntryZero

/-! Literal scan from the prepared state-76 HALF parser to a selected zero
fourth bank block, preserving the supplied bank suffix. -/
namespace Shared.Beeping.NPcoNP.NativeHalf159Scan
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeRightDispatchGeneric
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
open Shared.Beeping.NPcoNP.NativeRow13Scan
open Shared.Beeping.NPcoNP.NativeFirstNextPath
open Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
open Shared.Beeping.NPcoNP.NativeHalfEntryZero
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000

theorem scan47 (n : Nat) (h : Int) (t : Int → Bool)
    (ones : ∀ i : Nat, i<n → t (h+(i : Int))=true)
    (zero : t (h+(n : Int))=false) :
    silentSegment machine (cfg 47 h t) (cfg 46 (h+(n : Int)+1) t) (n+1) := by
  induction n generalizing h with
  | zero =>
    have hz : t h=false := by simpa using zero
    simpa using oneSeg machine _ _ (unchanged_right 47 46 false h t (by decide) hz)
  | succ n ih =>
    have ho : t h=true := by simpa using ones 0 (by omega)
    have hr : ∀ i : Nat, i<n → t ((h+1)+(i : Int))=true := by
      intro i hi
      have hh := ones (i+1) (by omega)
      simpa [Nat.cast_add,Int.add_assoc,Int.add_comm,Int.add_left_comm] using hh
    have hz : t ((h+1)+(n : Int))=false := by
      simpa [Nat.cast_add,Int.add_assoc,Int.add_comm,Int.add_left_comm] using zero
    have first := oneSeg machine _ _ (unchanged_right 47 47 true h t (by decide) ho)
    have next := ih (h+1) hr hz
    have all := segAdd machine _ _ _ 1 (n+1) first next
    convert all using 1 <;> simp [Nat.cast_add,Int.add_assoc,Int.add_comm,Int.add_left_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem prepared_to_selected_zero (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (entry : operationEntry name=some 76)
    (origin h separator : Int) (t : Int → Bool) (tail : List Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+3≤separator)
    (word : Holds t origin path) (marker : t h=true) (z1 : t (h+1)=false)
    (control : ∀ q, h+2≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) ([true,false,true,false,true,false,true,false] ++ tail)) :
    let out := clearAt h t
    ∃ steps : Nat, 0<steps ∧ Holds out (separator+1) ([true,false,true,false,true,false,true,false] ++ tail) ∧
      out (separator+7)=true ∧ out (separator+8)=false ∧
      (∀ q, q≠h → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 29 (separator+7) out) steps := by
  dsimp only
  let out := clearAt h t
  have member := graph_leaf_member state path name leaf
  have walk : PreparedWalk path (.op name) := expanded_leaf_follows traceState557.acc producerExpand (path,name) member
  obtain ⟨_,tailPath⟩ := prepared_head_tail t origin path name walk word
  have hdispatch := expanded_leaf_dispatch_to_entry traceState557.acc producerExpand (path,name) member 76 entry
    (origin+1) t tailPath
  have hlenPath : (path.tail.length : Int)+1=(path.length : Int) := by
    obtain ⟨raw,he,_⟩ := walk
    rw [he]
    simp [preparedPrefix]
  have hdispatch' : silentSegment machine (cfg 93 (origin+1) t) (cfg 76 h t) path.tail.length := by
    have he : origin+1+(path.tail.length : Int)=h := by omega
    simpa only [he] using hdispatch
  have h76 : machine.step (cfg 76 h t)=(cfg 48 (h+1) out,false) := by
    have row : machine.table.row 76 true=⟨false,.right,48,false⟩ := by decide
    have hw : (⟨76,h,t⟩ : Config 284).write false=out := rfl
    simp [cfg,Machine.step,marker,row,Move.apply,hw]
  have hz1 : out (h+1)=false := by simpa [out,clearAt,show h+1≠h by omega] using z1
  have h48 := oneSeg machine _ _ (unchanged_right 48 47 false (h+1) out (by decide) hz1)
  have h48' : silentSegment machine (cfg 48 (h+1) out) (cfg 47 (h+2) out) 1 := by
    simpa only [show h+1+1=h+2 by omega] using h48
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
  have hscan := scan47 r (h+2) out hones hz
  have hscan' : silentSegment machine (cfg 47 (h+2) out) (cfg 46 (separator+1) out) (r+1) := by
    have he : h+2+(r : Int)+1=separator+1 := by omega
    simpa only [he] using hscan
  have hbank : Holds out (separator+1) ([true,false,true,false,true,false,true,false] ++ tail) := by
    apply holds_transport t out (separator+1) _ bank
    intro p hp _
    simp [out,clearAt,show p≠h by omega]
  have hv := hbank
  simp only [List.cons_append,Holds] at hv
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,_⟩ := hv
  have b1' : out (separator+2)=false := by simpa only [show separator+1+1=separator+2 by omega] using b1
  have b2' : out (separator+3)=true := by simpa only [show separator+1+1+1=separator+3 by omega] using b2
  have b3' : out (separator+4)=false := by simpa only [show separator+1+1+1+1=separator+4 by omega] using b3
  have b4' : out (separator+5)=true := by simpa only [show separator+1+1+1+1+1=separator+5 by omega] using b4
  have b5' : out (separator+6)=false := by simpa only [show separator+1+1+1+1+1+1=separator+6 by omega] using b5
  have b6' : out (separator+7)=true := by simpa only [show separator+1+1+1+1+1+1+1=separator+7 by omega] using b6
  have b7' : out (separator+8)=false := by simpa only [show separator+1+1+1+1+1+1+1+1=separator+8 by omega] using b7
  have s0 : silentSegment machine (cfg 46 (separator+1) out) (cfg 45 (separator+3) out) 2 := by
    have hh := Shared.Beeping.NPcoNP.NativeHalf143Scan.scan46 1 (separator+1) out
      (by intro i hi; have he : i=0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi); simpa [he] using b0) (by simpa [Int.add_assoc] using b1')
    simpa only [Nat.cast_one,show separator+1+1+1=separator+3 by omega] using hh
  have s1 : silentSegment machine (cfg 45 (separator+3) out) (cfg 44 (separator+5) out) 2 := by
    have hh := scan45 1 (separator+3) out
      (by intro i hi; have he : i=0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi); simpa [he] using b2') (by simpa [Int.add_assoc] using b3')
    simpa only [Nat.cast_one,show separator+3+1+1=separator+5 by omega] using hh
  have s2 : silentSegment machine (cfg 44 (separator+5) out) (cfg 29 (separator+7) out) 2 := by
    have hh := scan44 1 (separator+5) out
      (by intro i hi; have he : i=0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi); simpa [he] using b4') (by simpa [Int.add_assoc] using b5')
    simpa only [Nat.cast_one,show separator+5+1+1=separator+7 by omega] using hh
  have b := segAdd machine _ _ _ path.tail.length 1 hdispatch' (oneSeg machine _ _ h76)
  have c := segAdd machine _ _ _ _ 1 b h48'
  have d := segAdd machine _ _ _ _ (r+1) c hscan'
  have e := segAdd machine _ _ _ _ 2 d s0
  have f := segAdd machine _ _ _ _ 2 e s1
  refine ⟨path.tail.length+1+1+(r+1)+2+2+2,by omega,hbank,b6',b7',?_,segAdd machine _ _ _ _ 2 f s2⟩
  intro p hp
  simp [clearAt,hp]

#print axioms prepared_to_selected_zero
end Shared.Beeping.NPcoNP.NativeHalf159Scan
