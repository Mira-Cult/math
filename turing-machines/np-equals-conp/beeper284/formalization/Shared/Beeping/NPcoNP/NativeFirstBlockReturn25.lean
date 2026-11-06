import Shared.Beeping.NPcoNP.NativeFirstReturn25
import Shared.Beeping.NPcoNP.Native271ZeroWindow

/-! Literal state-25 return when the just-restored target was the first bank
block. The theorem is conditional on its supplied finite control layout. -/
namespace Shared.Beeping.NPcoNP.NativeFirstBlockReturn25
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfOddReturn
open Shared.Beeping.NPcoNP.NativeHalfOddFinish
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeZeroRestoreWindow
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- The literal return starts at the separator and reaches state 1 at the
control position with no tape changes and a finite exact duration. -/
theorem return25_first_block (h separator : Int) (t : Int → Bool)
    (hlong : h+7≤separator)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false) (hp3 : t (h+3)=false)
    (control : ∀ q, h+4≤q → q<separator → t q=true)
    (hsep : t separator=false) :
    let k := (separator-(h+5)).toNat
    silentSegment machine (cfg 25 separator t) (cfg 1 h t) (k+5) := by
  dsimp only
  let k := (separator-(h+5)).toNat
  let ys := List.replicate k true
  have hk : (k : Int)=separator-(h+5) := Int.toNat_of_nonneg (by omega)
  have hc : Holds t (h+5) ys := by
    apply holds_ones
    intro i hi
    apply control <;> omega
  have hend : Holds t (h+5+(ys.length : Int)) [false] := by
    have he : h+5+(ys.length : Int)=separator := by simp [ys]; omega
    simpa [Holds,he] using hsep
  have hyEnd := holds_append_intro t (h+5) ys [false] hc hend
  have hp4 : t (h+4)=true := control (h+4) (by omega) (by omega)
  have hforward : Holds t (h+2) ([false,false,true] ++ ys ++ [false]) := by
    change t (h+2)=false ∧ t (h+2+1)=false ∧ t (h+2+1+1)=true ∧
      Holds t (h+2+1+1+1) (ys ++ [false])
    have he1 : h+2+1=h+3 := by omega
    have he2 : h+3+1=h+4 := by omega
    have he3 : h+4+1=h+5 := by omega
    simpa only [he1,he2,he3] using And.intro hp2 (And.intro hp3 (And.intro hp4 hyEnd))
  have hback := holds_reverse t (h+2) ([false,false,true] ++ ys ++ [false]) hforward
  let xs := false :: (ys.reverse ++ [true])
  have hrep : List.replicate k true ++ [true] = true :: List.replicate k true := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ,ih]
  have hx : Prefix xs := by
    have he : xs = false :: true :: List.replicate k true := by simp [xs,ys,hrep]
    rw [he]
    exact Prefix.zeroOne (prefix_ones k)
  have hstart : h+2+((([false,false,true] ++ ys ++ [false]).length : Nat) : Int)-1=separator := by
    simp only [List.length_append,List.length_cons,List.length_nil,ys,List.length_replicate,Nat.cast_add,Nat.cast_ofNat]
    omega
  have hwback : ([false,false,true] ++ ys ++ [false]).reverse=xs ++ [false,false] := by
    simp [xs,List.reverse_append,List.append_assoc]
  rw [hstart,hwback] at hback
  obtain ⟨s,hs⟩ := shape_of_prefix xs hx
  have hscan := return_scan25 s separator t (by simpa only [hs] using hback)
  have hslen : (bits s).length=k+2 := by
    rw [hs]
    simp [xs,ys]
  have hfinish : separator-((bits s).length : Int)-2=h+1 := by rw [hslen]; push_cast; omega
  have hscan' : silentSegment machine (cfg 25 separator t) (cfg 95 (h+1) t)
      ((bits s).length+2) := by simpa only [hfinish] using hscan
  have h95 := oneSeg machine _ _ (step95_zero (h+1) t hp1)
  have h95' : silentSegment machine (cfg 95 (h+1) t) (cfg 1 h t) 1 := by
    have he : h+1-1=h := by omega
    simpa only [he] using h95
  have all := segAdd machine _ _ _ ((bits s).length+2) 1 hscan' h95'
  have htime : (bits s).length+2+1=k+5 := by rw [hslen]
  simpa only [htime] using all

#print axioms return25_first_block
end Shared.Beeping.NPcoNP.NativeFirstBlockReturn25
