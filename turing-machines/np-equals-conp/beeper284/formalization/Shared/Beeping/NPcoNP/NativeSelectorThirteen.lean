import Shared.Beeping.NPcoNP.NativeSelectorPrefixReturn

/-! The selector works with up to thirteen zeros in a supplied prefix: one
additional zero is still provided by the blank left tail. -/
namespace Shared.Beeping.NPcoNP.NativeSelectorThirteen
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
open Shared.Beeping.NPcoNP.NativeSelectorPrefixReturn
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem paddedPath_final_zero_13 (path : List Bool) (hz : path.count false≤13) :
    (runsAux 0 (paddedPath path)).2=0 := by
  have hpos : 0<14-path.count false := by omega
  have hn : 14-path.count false = (14-path.count false-1)+1 := by omega
  have he : paddedPath path = (path ++ List.replicate (14-path.count false-1) false) ++ [false] := by
    dsimp [paddedPath]
    conv_lhs => rw [hn,List.replicate_succ']
    simp [List.append_assoc]
  rw [he]
  exact runsAux_ends_zero 0 _

theorem paddedPath_blocks_13 (path : List Bool) (hz : path.count false≤13) :
    blocks (pathRuns path)=paddedPath path := by
  have h := runsAux_word 0 (paddedPath path)
  rw [paddedPath_final_zero_13 path hz] at h
  simpa [pathRuns] using h

theorem pathRuns_length_13 (path : List Bool) (hz : path.count false≤13) :
    (pathRuns path).length=14 := by
  have h := runsAux_length 0 (paddedPath path)
  change (pathRuns path).length = (paddedPath path).count false at h
  simp only [paddedPath,List.count_append,List.count_replicate_self] at h
  omega

theorem selector_returns_to_origin_13 (t : Int → Bool) (origin : Int) (xs : List Bool)
    (count : xs.count false≤13) (word : Holds t origin xs)
    (left : ∀ q, q<origin → t q=false) (first : t origin=true) :
    ∃ steps, 0<steps ∧
      silentSegment machine (cfg 83 (origin+((xs.length : Nat) : Int)-1) t)
        (cfg 93 (origin+1) t) steps := by
  let r := 14-xs.count false
  let w := paddedPath xs.reverse
  let start := origin+((xs.length : Nat) : Int)-1
  have hc : xs.reverse.count false≤13 := by simpa using count
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
    (pathRuns_length_13 xs.reverse hc) (by simpa [paddedPath_blocks_13 xs.reverse hc] using hw)).2
  have hblocks : blocks (pathRuns xs.reverse)=w := paddedPath_blocks_13 xs.reverse hc
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

#print axioms selector_returns_to_origin_13
end Shared.Beeping.NPcoNP.NativeSelectorThirteen
