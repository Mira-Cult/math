import Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
import Shared.Beeping.NPcoNP.NativeIncBank

/-! A selector scan of thirteen unary blocks and one adjacent blank. -/
namespace Shared.Beeping.NPcoNP.NativeMarkerExtraZeroReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep

open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow

open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

theorem blocks_append (xs ys : List Nat) : blocks (xs ++ ys)=blocks xs ++ blocks ys := by
  induction xs with
  | nil => simp [blocks]
  | cons x xs ih => simp [blocks,ih,List.append_assoc]

/-- Thirteen ordinary unary blocks plus an adjacent blank give the fourteen
physical delimiters consumed by the literal leftward selector. -/
theorem marker_window_extra_zero_to92 (t : Int → Bool) (a : Int) (xs : List Nat)
    (hl : xs.length=13) (hz : t (a-1)=false) (window : Holds t a (markerWindow xs)) :
    silentSegment machine (cfg 83 (a+((encode xs).length : Int)-1) t)
      (cfg 92 (a-2) t) ((encode xs).length+1) := by
  have hw : Holds t (a-1) (false :: markerWindow xs) := by
    change t (a-1)=false ∧ Holds t (a-1+1) (markerWindow xs)
    exact ⟨hz,by simpa using window⟩
  have hd := holds_reverse t (a-1) (false :: markerWindow xs) hw
  have hd' : downHolds t (a+((encode xs).length : Int)-1) (encode xs.reverse ++ [false]) := by
    have hp : a-1+(((false :: markerWindow xs).length : Nat):Int)-1=
        a+((encode xs).length : Int)-1 := by simp
    rw [hp] at hd
    simpa [markerWindow] using hd
  let counts := xs.reverse.map (fun n => n+1) ++ [0]
  have hc : blocks counts=encode xs.reverse ++ [false] := by
    simp only [counts,blocks_append,blocks_encode,blocks,List.replicate_zero,List.nil_append,List.nil_append]
  have hcount : counts.length=14 := by simp [counts,hl]
  have hscan := (chain_blocks chain83 counts _ t [] hcount (by simpa [hc] using hd')).2
  have hlen : (blocks counts).length=(encode xs).length+1 := by
    rw [hc]
    simp [encode_length_reverse]
  rw [hlen] at hscan
  have hp : a+((encode xs).length : Int)-1-(((encode xs).length+1 : Nat):Int)=a-2 := by push_cast; omega
  simpa only [hp] using hscan

#print axioms marker_window_extra_zero_to92
end Shared.Beeping.NPcoNP.NativeMarkerExtraZeroReturn
