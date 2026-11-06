import Shared.Beeping.NPcoNP.Grammar284PathSelector
import Shared.Beeping.NPcoNP.NativeIncReturn23
import Shared.Beeping.NPcoNP.NativeFirstDispatch

/-! A selector beginning just left of a finite control prefix crosses the
prefix and the actual left blank tail, then returns to the prefix's first one.
This does not identify a graph successor. -/
namespace Shared.Beeping.NPcoNP.NativeSelectorPrefixReturn
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeIncReturn23
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.Grammar284PathSelector
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- A left blank tail supplies any finite descending word of zeros. -/
theorem down_blank (t : Int → Bool) (origin : Int) (k : Nat)
    (left : ∀ q, q<origin → t q=false) :
    downHolds t (origin-1) (List.replicate k false) := by
  have aux : ∀ (k : Nat) (h : Int), h<origin → downHolds t h (List.replicate k false) := by
    intro k
    induction k with
    | zero => intro h hh; trivial
    | succ k ih =>
      intro h hh
      simpa only [List.replicate_succ,downHolds] using And.intro (left h hh) (ih (h-1) (by omega))
  exact aux k (origin-1) (by omega)

/-- If a control prefix contains at most eleven zeros and starts at the first
one after a blank tail, the fourteen-block selector beginning just to its
right returns to that first one in finite positive silent time. -/
theorem selector_returns_to_origin (t : Int → Bool) (origin : Int) (xs : List Bool)
    (count : xs.count false≤11) (word : Holds t origin xs)
    (left : ∀ q, q<origin → t q=false) (first : t origin=true) :
    ∃ steps, 0<steps ∧
      silentSegment machine (cfg 83 (origin+((xs.length : Nat) : Int)-1) t)
        (cfg 93 (origin+1) t) steps := by
  let r := 14-xs.count false
  let w := paddedPath xs.reverse
  let start := origin+((xs.length : Nat) : Int)-1
  have hc : xs.reverse.count false≤11 := by simpa using count
  have hlen : w.length=xs.length+r := by simp [w,paddedPath,r]
  have hrev : downHolds t start xs.reverse := by
    simpa only [start] using holds_reverse t origin xs word
  have hblank : downHolds t (start-(xs.reverse.length : Int)) (List.replicate r false) := by
    have he : start-(xs.reverse.length : Int)=origin-1 := by simp [start]; omega
    rw [he]
    exact down_blank t origin r left
  have hw : downHolds t start w := by
    have hp := down_append t start xs.reverse (List.replicate r false) hrev hblank
    simpa [w,paddedPath,r] using hp
  have hscan := (chain_blocks chain83 (pathRuns xs.reverse) start t []
    (pathRuns_length xs.reverse hc) (by simpa [paddedPath_blocks xs.reverse hc] using hw)).2
  have hblocks : blocks (pathRuns xs.reverse)=w := paddedPath_blocks xs.reverse hc
  rw [hblocks] at hscan
  have hscan' : silentSegment machine (cfg 83 start t) (cfg 92 (origin-1-(r : Int)) t) w.length := by
    have he : start-(w.length : Int)=origin-1-(r : Int) := by rw [hlen]; dsimp [start]; omega
    simpa only [he] using hscan
  have hz : ∀ i : Nat, i<r+1 → t ((origin-1-(r : Int))+(i : Int))=false := by
    intro i hi
    apply left
    omega
  have ho : t ((origin-1-(r : Int))+((r+1 : Nat) : Int))=true := by
    have he : (origin-1-(r : Int))+((r+1 : Nat) : Int)=origin := by push_cast; omega
    simpa only [he] using first
  have hnext := scan92_exact (r+1) (origin-1-(r : Int)) t hz ho
  have hnext' : silentSegment machine (cfg 92 (origin-1-(r : Int)) t) (cfg 93 (origin+1) t) (r+2) := by
    have he : (origin-1-(r : Int))+((r+1 : Nat) : Int)+1=origin+1 := by push_cast; omega
    simpa only [he,show r+1+1=r+2 by omega] using hnext
  exact ⟨w.length+(r+2),by omega,segAdd machine _ _ _ w.length (r+2) hscan' hnext'⟩

#print axioms selector_returns_to_origin
end Shared.Beeping.NPcoNP.NativeSelectorPrefixReturn
