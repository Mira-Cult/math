import Shared.Beeping.NPcoNP.NativeFirstZeroRestored
import Shared.Beeping.NPcoNP.NativeHalfOddReturn
import Shared.Beeping.NPcoNP.NativeHalfOddFinish

/-! The restored zero-bank boundary returns to the state-1 carry entry in
finite silent time. The tape layout is explicit and no graph PC relation is
assumed. -/
namespace Shared.Beeping.NPcoNP.NativeFirstReturn25
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfOddReturn
open Shared.Beeping.NPcoNP.NativeHalfOddFinish
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeZeroRestoreWindow
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def fiveSuffix : List Bool := [false,true,false,true,false,true,false,true,false,true]

theorem reverse_word (r : Nat) :
    (unaryBankPrefix r (List.replicate 5 0)).reverse =
      true :: ((encode (List.replicate 5 0)).reverse ++ List.replicate r true) := by
  have hrep : List.replicate r true ++ [true] = true :: List.replicate r true := by
    induction r with
    | zero => rfl
    | succ r ih => simp [List.replicate_succ,ih]
  simp [unaryBankPrefix,encode,block,List.replicate_succ,List.reverse_append,hrep]

theorem return_prefix (r : Nat) :
    Prefix (false :: ((unaryBankPrefix r (List.replicate 5 0)).reverse ++ [true])) := by
  rw [reverse_word]
  change Prefix (false :: true :: (((encode (List.replicate 5 0)).reverse ++
    List.replicate r true) ++ [true]))
  apply Prefix.zeroOne
  apply prefix_append (prefix_reverse_bank (List.replicate 5 0))
  apply prefix_append (prefix_ones r)
  exact Prefix.one Prefix.nil

/-- Under the restored finite control and bank window, state 25 reaches
state 1 with the original tape after a positive finite silent segment. -/
theorem return25_to1_local (h separator : Int) (t : Int → Bool) (tail : List Bool)
    (hlong : h+7≤separator)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false) (hp3 : t (h+3)=false)
    (control : ∀ q, h+4≤q → q<separator → t q=true)
    (hsep : t separator=false)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail))) :
    let r := (separator-(h+6)).toNat
    let ys := unaryBankPrefix r (List.replicate 5 0)
    silentSegment machine (cfg 25 (separator+10) t) (cfg 1 h t) (ys.length+5) := by
  dsimp only
  let r := (separator-(h+6)).toNat
  let ys := unaryBankPrefix r (List.replicate 5 0)
  have hr : (r : Int)=separator-(h+6) := Int.toNat_of_nonneg (by omega)
  have hk : h+5+((r+1 : Nat) : Int)=separator := by push_cast; omega
  have hlen : ys.length=r+11 := by simp [ys,unaryBankPrefix,List.replicate_succ]
  have hc : Holds t (h+5) (List.replicate (r+1) true) := by
    apply holds_ones
    intro i hi
    apply control <;> omega
  have hfive : Holds t (separator+1) (encode (List.replicate 5 0)) :=
    holds_prefix_word t (separator+1) _ (block 0 ++ tail) bank
  have hbank : Holds t separator (false :: encode (List.replicate 5 0)) := by
    exact ⟨hsep,hfive⟩
  have heq : false :: encode (List.replicate 5 0) = fiveSuffix ++ [false] := by decide
  rw [heq] at hbank
  have hsuffix : Holds t separator fiveSuffix := holds_prefix_word t separator fiveSuffix [false] hbank
  have hy := holds_append_intro t (h+5) (List.replicate (r+1) true) fiveSuffix hc
    (by simpa only [List.length_replicate,hk] using hsuffix)
  have hyword : ys=List.replicate (r+1) true ++ fiveSuffix := by
    simp [ys,unaryBankPrefix,fiveSuffix,List.replicate_succ,List.append_assoc]
  rw [←hyword] at hy
  have hlast : t (separator+10)=false := by
    have hg := holds_get t (separator+1) (encode (List.replicate 5 0)) hfive 9 (by decide)
    have he : separator+1+(9 : Int)=separator+10 := by omega
    simpa [he,encode,block,List.replicate_succ] using hg
  have hend : Holds t (h+5+(ys.length : Int)) [false] := by
    have he : h+5+(ys.length : Int)=separator+10 := by rw [hlen]; push_cast; omega
    simpa [Holds,he] using hlast
  have hyEnd := holds_append_intro t (h+5) ys [false] hy hend
  have hp1' : t (h+1)=false := hp1
  have hp2' : t (h+2)=false := hp2
  have hp3' : t (h+3)=false := hp3
  have hp4' : t (h+4)=true := control (h+4) (by omega) (by omega)
  have hforward : Holds t (h+2) ([false,false,true] ++ ys ++ [false]) := by
    change t (h+2)=false ∧ t (h+2+1)=false ∧ t (h+2+1+1)=true ∧
      Holds t (h+2+1+1+1) (ys ++ [false])
    have he1 : h+2+1=h+3 := by omega
    have he2 : h+3+1=h+4 := by omega
    have he3 : h+4+1=h+5 := by omega
    simpa only [he1,he2,he3] using And.intro hp2' (And.intro hp3' (And.intro hp4' hyEnd))
  have hback := holds_reverse t (h+2) ([false,false,true] ++ ys ++ [false]) hforward
  let xs := false :: (ys.reverse ++ [true])
  have hx : Prefix xs := by simpa [xs,ys] using return_prefix r
  have hstart : h+2+((([false,false,true] ++ ys ++ [false]).length : Nat) : Int)-1=separator+10 := by
    simp only [List.length_append,List.length_cons,List.length_nil,hlen,Nat.cast_add,Nat.cast_ofNat]
    omega
  have hwback : ([false,false,true] ++ ys ++ [false]).reverse=xs ++ [false,false] := by
    simp [xs,List.reverse_append,List.append_assoc]
  rw [hstart,hwback] at hback
  obtain ⟨s,hs⟩ := shape_of_prefix xs hx
  have hscan := return_scan25 s (separator+10) t (by simpa only [hs] using hback)
  have hslen : (bits s).length=ys.length+2 := by
    rw [hs]
    simp [xs]
  have hfinish : separator+10-((bits s).length : Int)-2=h+1 := by rw [hslen,hlen]; push_cast; omega
  have hscan' : silentSegment machine (cfg 25 (separator+10) t) (cfg 95 (h+1) t)
      ((bits s).length+2) := by simpa only [hfinish] using hscan
  have h95 := oneSeg machine _ _ (step95_zero (h+1) t hp1')
  have h95' : silentSegment machine (cfg 95 (h+1) t) (cfg 1 h t) 1 := by
    have he : h+1-1=h := by omega
    simpa only [he] using h95
  have all := segAdd machine _ _ _ ((bits s).length+2) 1 hscan' h95'
  have htime : (bits s).length+2+1=ys.length+5 := by rw [hslen]
  simpa only [htime] using all

/-- The original nine-bit interface remains a projection of the local return. -/
theorem return25_to1 (h separator : Int) (t : Int → Bool) (tail : List Bool)
    (hlong : h+7≤separator)
    (word : Holds t (h-4) [true,true,false,true,false,false,false,false,true])
    (control : ∀ q, h+4≤q → q<separator → t q=true)
    (hsep : t separator=false)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail))) :
    let r := (separator-(h+6)).toNat
    let ys := unaryBankPrefix r (List.replicate 5 0)
    silentSegment machine (cfg 25 (separator+10) t) (cfg 1 h t) (ys.length+5) := by
  have hw := word
  simp only [Holds] at hw
  obtain ⟨_,_,_,_,_,hp1,hp2,hp3,_,_⟩ := hw
  have hp1' : t (h+1)=false := by convert hp1 using 1 <;> congr 1 <;> omega
  have hp2' : t (h+2)=false := by convert hp2 using 1 <;> congr 1 <;> omega
  have hp3' : t (h+3)=false := by convert hp3 using 1 <;> congr 1 <;> omega
  exact return25_to1_local h separator t tail hlong hp1' hp2' hp3' control hsep bank

#print axioms return25_to1_local
#print axioms reverse_word
#print axioms return_prefix
#print axioms return25_to1
end Shared.Beeping.NPcoNP.NativeFirstReturn25
