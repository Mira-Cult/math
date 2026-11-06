import Shared.Beeping.NPcoNP.NativeMarkerExtraZeroReturn
import Shared.Beeping.NPcoNP.NativeFirstDispatch

/-! Variable numbers of unary selector blocks preceded by a blank ray. -/
namespace Shared.Beeping.NPcoNP.NativeVariableMarkerReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeMarkerExtraZeroReturn
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

theorem blocks_zeroes (z : Nat) : blocks (List.replicate z 0)=List.replicate z false := by
  induction z with
  | zero => rfl
  | succ z ih => simp [List.replicate_succ,blocks,ih]

/-- A selector with at most fourteen unary blocks, a blank ray immediately to
its left, and an initial zero-one pair returns to state 93. The exact count
includes the additional physical blank delimiters. -/
theorem variable_marker_return (t : Int → Bool) (a : Int) (xs : List Nat)
    (hcount : xs.length≤14) (window : Holds t a (markerWindow xs))
    (blank : ∀ q, q<a → t q=false) (first0 : t a=false) (first1 : t (a+1)=true) :
    silentSegment machine (cfg 83 (a+((encode xs).length : Int)-1) t) (cfg 93 (a+2) t)
      ((encode xs).length+2*(14-xs.length)+3) := by
  let z := 14-xs.length
  let word := List.replicate z false ++ markerWindow xs
  let counts := xs.reverse.map (fun n => n+1) ++ List.replicate z 0
  have hz : xs.length+z=14 := by dsimp [z]; omega
  have hzeros : Holds t (a-(z : Int)) (List.replicate z false) := by
    apply holds_of_get
    intro i hi
    have hi' : i<z := by simpa using hi
    simp only [List.getElem_replicate]
    apply blank
    omega
  have hword : Holds t (a-(z : Int)) word := by
    apply holds_append_intro t (a-(z : Int)) (List.replicate z false) (markerWindow xs) hzeros
    have hp : a-(z : Int)+((List.replicate z false).length : Int)=a := by simp
    rw [hp]
    exact window
  have hlen : word.length=z+(encode xs).length := by simp [word]
  have hreverse : word.reverse=blocks counts := by
    simp only [word,List.reverse_append,List.reverse_replicate,markerWindow,List.reverse_reverse,
      counts,blocks_append,blocks_encode,blocks_zeroes]
  have hd := holds_reverse t (a-(z : Int)) word hword
  rw [hreverse,hlen] at hd
  have hp : a-(z : Int)+((z+(encode xs).length : Nat):Int)-1=
      a+((encode xs).length : Int)-1 := by push_cast; omega
  rw [hp] at hd
  have hcounts : counts.length=14 := by simp [counts,hz]
  have hscan := (chain_blocks chain83 counts _ t [] hcounts (by simpa using hd)).2
  have hblocks : (blocks counts).length=z+(encode xs).length := by
    have hh := congrArg List.length hreverse
    simpa only [List.length_reverse,hlen] using hh.symm
  rw [hblocks] at hscan
  have hscan' : silentSegment machine (cfg 83 (a+((encode xs).length : Int)-1) t)
      (cfg 92 (a-(z : Int)-1) t) ((encode xs).length+z) := by
    have hp' : a+((encode xs).length : Int)-1-((z+(encode xs).length : Nat):Int)=a-(z : Int)-1 := by push_cast; omega
    simpa only [hp',Nat.add_comm] using hscan
  have h92 := scan92_exact (z+2) (a-(z : Int)-1) t (by
    intro i hi
    by_cases hi0 : i=z+1
    · have hp' : a-(z : Int)-1+(i : Int)=a := by omega
      rw [hp']; exact first0
    · apply blank
      omega) (by
      have hp' : a-(z : Int)-1+((z+2 : Nat):Int)=a+1 := by push_cast; omega
      simpa only [hp'] using first1)
  have h92' : silentSegment machine (cfg 92 (a-(z : Int)-1) t) (cfg 93 (a+2) t) (z+3) := by
    have hp' : a-(z : Int)-1+((z+2 : Nat):Int)+1=a+2 := by push_cast; omega
    have hc : z+2+1=z+3 := by omega
    simpa only [hp',hc] using h92
  have hall := segAdd machine _ _ _ ((encode xs).length+z) (z+3) hscan' h92'
  have hc : (encode xs).length+z+(z+3)=(encode xs).length+2*z+3 := by omega
  simpa only [hc,z] using hall

#print axioms variable_marker_return
end Shared.Beeping.NPcoNP.NativeVariableMarkerReturn
