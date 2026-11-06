import Shared.Beeping.NPcoNP.NativeHalfCleanupSweep
import Shared.Beeping.NPcoNP.NativeHalfCleanupShape
import Shared.Beeping.NPcoNP.NativeHalfExceptionalScan

/-! Composition from the exceptional prepared boundary through both cleanup
scans. This does not establish blank-start reachability or selector return. -/
namespace Shared.Beeping.NPcoNP.NativeHalfCleanupComposed
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfCleanupSweep
open Shared.Beeping.NPcoNP.NativeHalfCleanupShape
open Shared.Beeping.NPcoNP.NativeHalfExceptionalScan
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.UnarySuffixShift
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- A prepared exceptional boundary reaches state 23 in positive finite time,
without any beep. The post-tape is the exact reverse-sweep specification. -/
theorem exceptional_through_cleanup (base : Int → Bool) (b : Int) (values : List Nat)
    (hb : base b = true) :
    let suffix := false :: UnaryBank.encode values
    let p := b + 3 + (suffix.length : Int)
    ∃ n : Nat, 0 < n ∧ silentSegment machine
      (cfg 30 b (prior base b suffix))
      (cfg 23 b (spec (after base (b+1) suffix) p ((UnaryBank.encode values).length + 2))) n := by
  dsimp only
  obtain ⟨s, hs⟩ := cleanup_shape values
  have hm := down_after_zero_bank base (b+1) values
  have hm' : downHolds (after base (b+1) (false :: UnaryBank.encode values))
      (b+3+((false :: UnaryBank.encode values).length : Int)) (bits s ++ [false,false]) := by
    simpa [hs, Int.add_assoc] using hm
  have he := exceptional_through_scan base b values hb
  have he' : silentSegment machine
      (cfg 30 b (prior base b (false :: UnaryBank.encode values)))
      (cfg 20 (b+3+((false :: UnaryBank.encode values).length : Int))
        (after base (b+1) (false :: UnaryBank.encode values))) (duration values) := by
    dsimp only at he
    have hp : b + 2 + ((((false :: UnaryBank.encode values) ++ [true]).length : Nat) : Int) =
        b + 3 + (((false :: UnaryBank.encode values).length : Nat) : Int) := by
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_succ, Nat.cast_zero]
      omega
    rw [hp] at he
    exact he
  have hsweep := cleanup_sweep s _ _ hm'
  have hlen : (bits s).length = (UnaryBank.encode values).length + 2 := by
    simp [hs] <;> omega
  have hsweep' : silentSegment machine
      (cfg 20 (b+3+((false :: UnaryBank.encode values).length : Int))
        (after base (b+1) (false :: UnaryBank.encode values)))
      (cfg 23 b (spec (after base (b+1) (false :: UnaryBank.encode values))
        (b+3+((false :: UnaryBank.encode values).length : Int))
        ((UnaryBank.encode values).length+2))) ((UnaryBank.encode values).length+4) := by
    rw [hlen] at hsweep
    have hp : b + 3 + (((false :: UnaryBank.encode values).length : Nat) : Int) -
        (((UnaryBank.encode values).length + 2 : Nat) : Int) - 2 = b := by
      simp only [List.length_cons, Nat.cast_succ, Nat.cast_add, Nat.cast_ofNat]
      omega
    rw [hp] at hsweep
    convert hsweep using 1 <;> omega
  refine ⟨duration values + ((UnaryBank.encode values).length+4), by have := duration_positive values; omega, ?_⟩
  exact segAdd machine _ _ _ _ _ he' hsweep'
end Shared.Beeping.NPcoNP.NativeHalfCleanupComposed
