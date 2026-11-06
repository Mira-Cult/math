import Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3328
import Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
import Shared.Beeping.NPcoNP.Bootstrap284BulkReplay

/-! Generated continuation; each asserted block requires Lean checking. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3584
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284PackedScans
open Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
open Shared.Beeping.NPcoNP.Bootstrap284TraceData
open Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3328
open Shared.Beeping.NPcoNP.Bootstrap284BulkReplay
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def startConfig : Packed := extendLeft 0 output3328
theorem start_segment : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 startConfig) 321380 := by
  have h : toConfig (-2048) 2056 startConfig=toConfig (-2048) 2056 output3328 := by
    simpa [startConfig] using toConfig_extendLeft (-2048) 2056 0 output3328
  rw [h]
  exact blank_start_3328

def output3360 : Packed := ⟨2,-1291,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3360 : replayBulk (-2048) 2056 ((ops.drop 3328).take 32) startConfig = some (output3360,2237) := by decide
theorem segment3360 : silentSegment machine (toConfig (-2048) 2056 startConfig) (toConfig (-2048) 2056 output3360) 2237 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3328).take 32) startConfig output3360 2237 checked3360).2
theorem blank_start_3360 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3360) 323617 := by
  have h := segAdd machine _ _ _ 321380 2237 start_segment segment3360
  simpa using h

def output3392 : Packed := ⟨0,-1689,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3392 : replayBulk (-2048) 2056 ((ops.drop 3360).take 32) output3360 = some (output3392,2786) := by decide
theorem segment3392 : silentSegment machine (toConfig (-2048) 2056 output3360) (toConfig (-2048) 2056 output3392) 2786 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3360).take 32) output3360 output3392 2786 checked3392).2
theorem blank_start_3392 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3392) 326403 := by
  have h := segAdd machine _ _ _ 323617 2786 blank_start_3360 segment3392
  simpa using h

def output3424 : Packed := ⟨0,-1704,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555500000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3424 : replayBulk (-2048) 2056 ((ops.drop 3392).take 32) output3392 = some (output3424,2549) := by decide
theorem segment3424 : silentSegment machine (toConfig (-2048) 2056 output3392) (toConfig (-2048) 2056 output3424) 2549 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3392).take 32) output3392 output3424 2549 checked3424).2
theorem blank_start_3424 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3424) 328952 := by
  have h := segAdd machine _ _ _ 326403 2549 blank_start_3392 segment3424
  simpa using h

def output3456 : Packed := ⟨2,-1720,0xf7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab8000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3456 : replayBulk (-2048) 2056 ((ops.drop 3424).take 32) output3424 = some (output3456,2694) := by decide
theorem segment3456 : silentSegment machine (toConfig (-2048) 2056 output3424) (toConfig (-2048) 2056 output3456) 2694 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3424).take 32) output3424 output3456 2694 checked3456).2
theorem blank_start_3456 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3456) 331646 := by
  have h := segAdd machine _ _ _ 328952 2694 blank_start_3424 segment3456
  simpa using h

def output3488 : Packed := ⟨4,-1254,0xf7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3488 : replayBulk (-2048) 2056 ((ops.drop 3456).take 32) output3456 = some (output3488,3318) := by decide
theorem segment3488 : silentSegment machine (toConfig (-2048) 2056 output3456) (toConfig (-2048) 2056 output3488) 3318 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3456).take 32) output3456 output3488 3318 checked3488).2
theorem blank_start_3488 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3488) 334964 := by
  have h := segAdd machine _ _ _ 331646 3318 blank_start_3456 segment3488
  simpa using h

def output3520 : Packed := ⟨2,-1243,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3520 : replayBulk (-2048) 2056 ((ops.drop 3488).take 32) output3488 = some (output3520,3005) := by decide
theorem segment3520 : silentSegment machine (toConfig (-2048) 2056 output3488) (toConfig (-2048) 2056 output3520) 3005 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3488).take 32) output3488 output3520 3005 checked3520).2
theorem blank_start_3520 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3520) 337969 := by
  have h := segAdd machine _ _ _ 334964 3005 blank_start_3488 segment3520
  simpa using h

def output3552 : Packed := ⟨0,-1769,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3552 : replayBulk (-2048) 2056 ((ops.drop 3520).take 32) output3520 = some (output3552,3682) := by decide
theorem segment3552 : silentSegment machine (toConfig (-2048) 2056 output3520) (toConfig (-2048) 2056 output3552) 3682 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3520).take 32) output3520 output3552 3682 checked3552).2
theorem blank_start_3552 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3552) 341651 := by
  have h := segAdd machine _ _ _ 337969 3682 blank_start_3520 segment3552
  simpa using h

def output3584 : Packed := ⟨0,-1784,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3584 : replayBulk (-2048) 2056 ((ops.drop 3552).take 32) output3552 = some (output3584,3317) := by decide
theorem segment3584 : silentSegment machine (toConfig (-2048) 2056 output3552) (toConfig (-2048) 2056 output3584) 3317 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3552).take 32) output3552 output3584 3317 checked3584).2
theorem blank_start_3584 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3584) 344968 := by
  have h := segAdd machine _ _ _ 341651 3317 blank_start_3552 segment3584
  simpa using h
end Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3584

#print axioms Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3584.blank_start_3584
