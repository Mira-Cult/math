import Shared.Beeping.NPcoNP.NativeHalf143ZeroReturn
import Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
import Shared.Beeping.NPcoNP.NativeHalfSweepShape
import Shared.Beeping.NPcoNP.NativeZeroRestoreWindow
import Shared.Beeping.NPcoNP.NativeIncBank
import Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch

/-! A zero-valued selected HALF bank block returns through an arbitrary
encoded prefix to the prepared control, without writing to the tape. -/
namespace Shared.Beeping.NPcoNP.NativeHalfZeroGeneralReturn
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfOddReturn
open Shared.Beeping.NPcoNP.NativeHalfOddFinish
open Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
open Shared.Beeping.NPcoNP.NativeHalfEntryZero
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeZeroRestoreWindow
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem selected_zero_returns (h separator : Int) (t : Int → Bool) (values : List Nat) (tail : List Bool)
    (space : h+3≤separator) (z0 : t h=false) (z1 : t (h+1)=false) (prev : t (h-1)=false)
    (control : ∀ q, h+2≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ ([true,false] ++ tail))) :
    let pos := separator+1+((encode values).length : Int)
    ∃ steps : Nat, 0<steps ∧
      silentSegment machine (cfg 29 pos t) (cfg 1 (h-2) t) steps := by
  dsimp only
  let pos := separator+1+((encode values).length : Int)
  obtain ⟨hb,hselected⟩ := holds_split t (separator+1) (encode values) ([true,false] ++ tail) bank
  have hs : t pos=true ∧ t (pos+1)=false := by
    simp only [List.cons_append,Holds] at hselected
    exact ⟨by simpa [pos] using hselected.1, by simpa [pos] using hselected.2.1⟩
  let r := (separator-h-3).toNat
  have hr : (r : Int)=separator-h-3 := Int.toNat_of_nonneg (by omega)
  let ones := List.replicate (r+1) true
  have hones : Holds t (h+2) ones := by
    apply holds_ones
    intro i hi
    exact control _ (by omega) (by omega)
  have hsepword : Holds t separator ([false] ++ encode values ++ [true]) := by
    have hb' : Holds t (separator+1) (encode values ++ [true]) := by
      apply holds_prefix t (separator+1) _ ([false] ++ tail)
      simpa [List.append_assoc] using bank
    change t separator=false ∧ Holds t (separator+1) (encode values ++ [true])
    exact ⟨sep,hb'⟩
  have hforward : Holds t h ([false,false] ++ ones ++ [false] ++ encode values ++ [true]) := by
    have hones' : Holds t (h+2) (ones ++ ([false] ++ encode values ++ [true])) := by
      apply holds_append_intro t (h+2) ones _ hones
      have he : h+2+(ones.length : Int)=separator := by simp [ones]; omega
      simpa only [he] using hsepword
    change t h=false ∧ t (h+1)=false ∧ Holds t (h+1+1) (ones ++ [false] ++ encode values ++ [true])
    simpa [show h+1+1=h+2 by omega,List.append_assoc] using And.intro z0 (And.intro z1 hones')
  let pre := [true] ++ (encode values).reverse ++ [false] ++ ones
  have hpre : Prefix pre := by
    have hrest : Prefix ([false] ++ ones) := by
      dsimp [ones]
      simp only [List.replicate_succ,List.cons_append]
      exact Prefix.zeroOne (prefix_ones r)
    dsimp [pre]
    simpa [List.append_assoc] using Prefix.one (prefix_append (prefix_reverse_bank values) hrest)
  obtain ⟨shape,hshape⟩ := shape_of_prefix pre hpre
  have hrev := holds_reverse t h ([false,false] ++ ones ++ [false] ++ encode values ++ [true]) hforward
  have hpos : h+(([false,false] ++ ones ++ [false] ++ encode values ++ [true]).length : Int)-1=pos := by
    dsimp [pos,ones]
    simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate,Nat.cast_add,Nat.cast_ofNat]
    omega
  have hrevword : ([false,false] ++ ones ++ [false] ++ encode values ++ [true]).reverse=pre ++ [false,false] := by
    simp [pre,List.reverse_append,ones,List.append_assoc]
  rw [hpos,hrevword,←hshape] at hrev
  have hret := return_scan25 shape pos t hrev
  have hshapeLen : ((bits shape).length : Int)=pos-h-1 := by
    rw [hshape]
    dsimp [pre,pos,ones]
    simp only [List.length_append,List.length_cons,List.length_nil,List.length_reverse,List.length_replicate,Nat.cast_add,Nat.cast_ofNat]
    omega
  have hret' : silentSegment machine (cfg 25 pos t) (cfg 95 (h-1) t) ((bits shape).length+2) := by
    have he : pos-((bits shape).length : Int)-2=h-1 := by omega
    simpa only [he] using hret
  have h0 := oneSeg machine _ _ (step29_one pos t hs.1)
  have h1 := oneSeg machine _ _ (step41_zero (pos+1) t hs.2)
  have h01 : silentSegment machine (cfg 29 pos t) (cfg 25 pos t) 2 := by
    simpa only [show pos+1-1=pos by omega] using segAdd machine _ _ _ 1 1 h0 h1
  have hend := oneSeg machine _ _ (step95_zero (h-1) t prev)
  have hend' : silentSegment machine (cfg 95 (h-1) t) (cfg 1 (h-2) t) 1 := by
    simpa only [show h-1-1=h-2 by omega] using hend
  exact ⟨2+((bits shape).length+2)+1,by omega,
    segAdd machine _ _ _ _ 1 (segAdd machine _ _ _ 2 _ h01 hret') hend'⟩

#print axioms selected_zero_returns
end Shared.Beeping.NPcoNP.NativeHalfZeroGeneralReturn
