import Shared.Beeping.NPcoNP.Bootstrap284PackedContinue2304
import Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
import Shared.Beeping.NPcoNP.Bootstrap284BulkReplay

/-! Generated continuation; each asserted block requires Lean checking. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284BulkContinue2560
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284PackedScans
open Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
open Shared.Beeping.NPcoNP.Bootstrap284TraceData
open Shared.Beeping.NPcoNP.Bootstrap284PackedContinue2304
open Shared.Beeping.NPcoNP.Bootstrap284BulkReplay
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def startConfig : Packed := extendLeft 0 output2304
theorem start_segment : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 startConfig) 163520 := by
  have h : toConfig (-2048) 2056 startConfig=toConfig (-2048) 2056 output2304 := by
    simpa [startConfig] using toConfig_extendLeft (-2048) 2056 0 output2304
  rw [h]
  exact blank_start_2304

def output2336 : Packed := ⟨0,-1162,0xeffffffffffffffffffffffffffffffffffffffffd555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2336 : replayBulk (-2048) 2056 ((ops.drop 2304).take 32) startConfig = some (output2336,6930) := by decide
theorem segment2336 : silentSegment machine (toConfig (-2048) 2056 startConfig) (toConfig (-2048) 2056 output2336) 6930 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2304).take 32) startConfig output2336 6930 checked2336).2
theorem blank_start_2336 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2336) 170450 := by
  have h := segAdd machine _ _ _ 163520 6930 start_segment segment2336
  simpa using h

def output2368 : Packed := ⟨0,-1177,0xeffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2368 : replayBulk (-2048) 2056 ((ops.drop 2336).take 32) output2336 = some (output2368,6101) := by decide
theorem segment2368 : silentSegment machine (toConfig (-2048) 2056 output2336) (toConfig (-2048) 2056 output2368) 6101 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2336).take 32) output2336 output2368 6101 checked2368).2
theorem blank_start_2368 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2368) 176551 := by
  have h := segAdd machine _ _ _ 170450 6101 blank_start_2336 segment2368
  simpa using h

def output2400 : Packed := ⟨2,-1193,0xeffffffffffffffffffffffffffffffffffff5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2400 : replayBulk (-2048) 2056 ((ops.drop 2368).take 32) output2368 = some (output2400,6246) := by decide
theorem segment2400 : silentSegment machine (toConfig (-2048) 2056 output2368) (toConfig (-2048) 2056 output2400) 6246 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2368).take 32) output2368 output2400 6246 checked2400).2
theorem blank_start_2400 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2400) 182797 := by
  have h := segAdd machine _ _ _ 176551 6246 blank_start_2368 segment2400
  simpa using h

def output2432 : Packed := ⟨4,-135,0xefffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2432 : replayBulk (-2048) 2056 ((ops.drop 2400).take 32) output2400 = some (output2432,7462) := by decide
theorem segment2432 : silentSegment machine (toConfig (-2048) 2056 output2400) (toConfig (-2048) 2056 output2432) 7462 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2400).take 32) output2400 output2432 7462 checked2432).2
theorem blank_start_2432 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2432) 190259 := by
  have h := segAdd machine _ _ _ 182797 7462 blank_start_2400 segment2432
  simpa using h

def output2464 : Packed := ⟨2,-124,0xefffffffffffffffffffffffffffffff5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2464 : replayBulk (-2048) 2056 ((ops.drop 2432).take 32) output2432 = some (output2464,6557) := by decide
theorem segment2464 : silentSegment machine (toConfig (-2048) 2056 output2432) (toConfig (-2048) 2056 output2464) 6557 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2432).take 32) output2432 output2464 6557 checked2464).2
theorem blank_start_2464 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2464) 196816 := by
  have h := segAdd machine _ _ _ 190259 6557 blank_start_2432 segment2464
  simpa using h

def output2496 : Packed := ⟨0,-1242,0xeffffffffffffffffffffffffffffd555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2496 : replayBulk (-2048) 2056 ((ops.drop 2464).take 32) output2464 = some (output2496,7826) := by decide
theorem segment2496 : silentSegment machine (toConfig (-2048) 2056 output2464) (toConfig (-2048) 2056 output2496) 7826 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2464).take 32) output2464 output2496 7826 checked2496).2
theorem blank_start_2496 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2496) 204642 := by
  have h := segAdd machine _ _ _ 196816 7826 blank_start_2464 segment2496
  simpa using h

def output2528 : Packed := ⟨0,-1257,0xeffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2528 : replayBulk (-2048) 2056 ((ops.drop 2496).take 32) output2496 = some (output2528,6869) := by decide
theorem segment2528 : silentSegment machine (toConfig (-2048) 2056 output2496) (toConfig (-2048) 2056 output2528) 6869 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2496).take 32) output2496 output2528 6869 checked2528).2
theorem blank_start_2528 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2528) 211511 := by
  have h := segAdd machine _ _ _ 204642 6869 blank_start_2496 segment2528
  simpa using h

def output2560 : Packed := ⟨2,-1273,0xeffffffffffffffffffffffff555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2560 : replayBulk (-2048) 2056 ((ops.drop 2528).take 32) output2528 = some (output2560,7014) := by decide
theorem segment2560 : silentSegment machine (toConfig (-2048) 2056 output2528) (toConfig (-2048) 2056 output2560) 7014 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2528).take 32) output2528 output2560 7014 checked2560).2
theorem blank_start_2560 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2560) 218525 := by
  have h := segAdd machine _ _ _ 211511 7014 blank_start_2528 segment2560
  simpa using h
end Shared.Beeping.NPcoNP.Bootstrap284BulkContinue2560

#print axioms Shared.Beeping.NPcoNP.Bootstrap284BulkContinue2560.blank_start_2560
