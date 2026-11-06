import Shared.Beeping.NPcoNP.Native54Redispatch
import Shared.Beeping.NPcoNP.NativeHalfScannerFrames

/-! Finite row-8 control preparation after a continuation return. -/
namespace Shared.Beeping.NPcoNP.Native54ReturnTo273
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.Native54Prepare
open Shared.Beeping.NPcoNP.Native54Redispatch
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

/-- The literal state-54 instruction prepares its control run, rediscovers
row 8, and enters state 273. The encoded bank suffix is untouched. -/
theorem prepare_and_enter (h separator : Int) (t : Int → Bool)
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false) (h7 : t (h+7)=false)
    (gap : ∀ q, h+7<q → q<separator-1 → t q=false)
    (marker : t (separator-1)=true) (sep : t separator=false) :
    let u := fillRange (setAt (h+7) t) (h+10) (separator-1)
    ∃ n : Nat, 0<n ∧ Holds u (h-4) fifthPath ∧
      (∀ q, q<h-4 → u q=false) ∧ u (h+7)=true ∧
      u (h+8)=false ∧ u (h+9)=false ∧
      (∀ q, h+10≤q → q<separator → u q=true) ∧ u separator=false ∧
      (∀ q, separator≤q → u q=t q) ∧
      silentSegment machine (cfg 54 (h+7) t) (cfg 273 (h+8) u) n := by
  dsimp only
  let r := (separator-(h+12)).toNat
  have hr : (r : Int)=separator-(h+12) := Int.toNat_of_nonneg (by omega)
  let k := r+1
  have hk : (k : Int)=separator-(h+11) := by dsimp [k]; push_cast; omega
  have hz8 : t (h+8)=false := gap _ (by omega) (by omega)
  have hz9 : t (h+9)=false := gap _ (by omega) (by omega)
  have hz : ∀ i : Nat, i<k → t ((h+7)+3+(i : Int))=false := by
    intro i hi
    apply gap <;> omega
  have hm : t ((h+7)+3+(k : Int))=true := by
    have he : (h+7)+3+(k : Int)=separator-1 := by omega
    rw [he]; exact marker
  let u := fillRange (setAt (h+7) t) (h+10) (separator-1)
  have he8 : h+7+1=h+8 := by omega
  have he9 : h+7+2=h+9 := by omega
  have hprep := zero_prepare_to83 (h+7) t k (by dsimp [k]; omega) h7
    (by simpa only [he8] using hz8) (by simpa only [he9] using hz9) hz hm
  have he1 : (h+7)+3+(k : Int)=separator-1 := by omega
  have he2 : (h+7)+3+(k : Int)-2=h+9+(r : Int) := by omega
  have he1' : h+10+(k : Int)=separator-1 := by omega
  have he2' : h+10+(k : Int)-2=h+9+(r : Int) := by omega
  have he4 : separator-1-2=h+9+(r : Int) := by omega
  have hseg : silentSegment machine (cfg 54 (h+7) t) (cfg 83 (h+9+(r : Int)) u) (k+5) := by
    simpa only [show (h+7)+3=h+10 by omega,he1',he2',he4,u] using hprep.2.2
  have hselect := selector_prepared h r t path left hz8 hz9
  have he3 : h+11+(r : Int)=separator-1 := by omega
  have hselect' : silentSegment machine (cfg 83 (h+9+(r : Int)) u) (cfg 93 (h-3) u) (r+30) := by
    simpa only [he3,u] using hselect
  have hframe : ∀ q, q≠h+7 → (q<h+10 ∨ separator-1≤q) → u q=t q := by
    intro q hne hq
    have hn : ¬ (h+10≤q ∧ q<separator-1) := by omega
    simp [u,fillRange,setAt,hne,hn]
  have hp : Holds u (h-4) fifthPath := by
    apply holds_transport t u _ _ path
    intro q hq hq'
    symm
    apply hframe q <;> simp [fifthPath] at hq' <;> omega
  have hl : ∀ q, q<h-4 → u q=false := by
    intro q hq
    rw [hframe q (by omega) (by omega)]
    exact left q hq
  have hmark : u (h+7)=true := by simp [u,fillRange,setAt]
  have h8 : u (h+8)=false := by rw [hframe _ (by omega) (by omega)]; exact hz8
  have h9 : u (h+9)=false := by rw [hframe _ (by omega) (by omega)]; exact hz9
  have hrun : ∀ q, h+10≤q → q<separator → u q=true := by
    intro q hq hq'
    by_cases he : q=separator-1
    · rw [he,hframe _ (by omega) (by omega)]; exact marker
    · have hp : h+10≤q ∧ q<separator-1 := by omega
      simp [u,fillRange,hp]
  have hs : u separator=false := by rw [hframe _ (by omega) (by omega)]; exact sep
  have hf : ∀ q, separator≤q → u q=t q := by
    intro q hq
    exact hframe q (by omega) (by omega)
  have hdispatch := dispatch_fifth_path h u hp
  have hone := oneSeg machine _ _ (step54_one (h+7) u hmark)
  have hone' : silentSegment machine (cfg 54 (h+7) u) (cfg 273 (h+8) u) 1 := by
    have he : h+7+1=h+8 := by omega
    simpa only [he] using hone
  have first := segAdd machine _ _ _ (k+5) (r+30) hseg hselect'
  have second := segAdd machine _ _ _ (k+5+(r+30)) 10 first hdispatch
  have all := segAdd machine _ _ _ (k+5+(r+30)+10) 1 second hone'
  exact ⟨k+5+(r+30)+10+1,by omega,hp,hl,hmark,h8,h9,hrun,hs,hf,all⟩

#print axioms prepare_and_enter
end Shared.Beeping.NPcoNP.Native54ReturnTo273
