import Shared.Beeping.NPcoNP.NativeHalfMaximalIteration
import Shared.Beeping.NPcoNP.NativeHalfCyclePrelude

namespace Shared.Beeping.NPcoNP.NativeHalfOddResidual
open Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.NativeHalfCyclePrelude

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem row43_zero : machine.table.row 43 false = ⟨false, .right, 37, false⟩ := by decide

theorem step43_zero (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 43 h t) = (cfg 37 (h+1) (put t h false), false) := by
  simp [Machine.step, cfg, ht, row43_zero, Move.apply]
  rfl

theorem residual_one_bits (base : Int → Bool) (g : Int) (xs : List Nat) :
    let t := after base g (UnaryBank.encode (0::xs))
    t g = false ∧ t (g+1) = true ∧ t (g+2) = false := by
  dsimp only
  constructor
  · exact (gap_cells base g (UnaryBank.encode (0::xs))).2.2
  constructor
  · have h := after_suffix_bit base g (UnaryBank.encode (0::xs)) 0 (by simp [UnaryBank.encode])
    simpa [UnaryBank.encode, UnaryBank.block, bitAt, Int.add_assoc] using h
  · have h := after_suffix_bit base g (UnaryBank.encode (0::xs)) 1 (by simp [UnaryBank.encode])
    simpa [UnaryBank.encode, UnaryBank.block, bitAt, Int.add_assoc] using h

theorem residual_one_step (base : Int → Bool) (g : Int) (xs : List Nat) :
    let t := after base g (UnaryBank.encode (0::xs))
    silentSegment machine (cfg 30 g t)
      (cfg 37 (g+3) (put (put (put t g true) (g+1) false) (g+2) false)) 3 := by
  dsimp only
  let t := after base g (UnaryBank.encode (0::xs))
  obtain ⟨h0,h1,h2⟩ := residual_one_bits base g xs
  have h1' : put t g true (g+1) = true := by
    rw [put_other _ _ _ _ (by omega)]
    exact h1
  have h2' : put (put t g true) (g+1) false (g+2) = false := by
    rw [put_other _ _ _ _ (by omega), put_other _ _ _ _ (by omega)]
    exact h2
  have s0 := oneSeg machine _ _ (step30 g t h0)
  have s1 := oneSeg machine _ _ (step40 (g+1) (put t g true) h1')
  have s2 := oneSeg machine _ _ (step43_zero (g+2) (put (put t g true) (g+1) false) h2')
  have h01 := segAdd machine _ _ _ 1 1 s0 s1
  have h012 := segAdd machine _ _ _ 2 1 (by simpa using h01) (by simpa [Int.add_assoc] using s2)
  simpa [Int.add_assoc] using h012
end Shared.Beeping.NPcoNP.NativeHalfOddResidual
