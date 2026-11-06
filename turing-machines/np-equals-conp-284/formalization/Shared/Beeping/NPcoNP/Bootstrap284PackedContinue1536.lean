import Shared.Beeping.NPcoNP.Bootstrap284PackedContinue1280
import Shared.Beeping.NPcoNP.Bootstrap284PackedRebase

/-! Generated continuation; each asserted block requires Lean checking. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284PackedContinue1536
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284PackedScans
open Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
open Shared.Beeping.NPcoNP.Bootstrap284TraceData
open Shared.Beeping.NPcoNP.Bootstrap284PackedContinue1280
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def startConfig : Packed := extendLeft 0 output1280
theorem start_segment : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 startConfig) 47389 := by
  have h : toConfig (-1024) 1032 startConfig=toConfig (-1024) 1032 output1280 := by
    simpa [startConfig] using toConfig_extendLeft (-1024) 1032 0 output1280
  rw [h]
  exact blank_start_1280

def output1312 : Packed := ⟨4,-471,0xefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1312 : replayPacked (-1024) 1032 ((ops.drop 1280).take 32) startConfig = some (output1312,1190) := by decide
theorem segment1312 : silentSegment machine (toConfig (-1024) 1032 startConfig) (toConfig (-1024) 1032 output1312) 1190 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1280).take 32) startConfig output1312 1190 checked1312).2
theorem blank_start_1312 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1312) 48579 := by
  have h := segAdd machine _ _ _ 47389 1190 start_segment segment1312
  simpa using h

def output1344 : Packed := ⟨2,-460,0xefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff555555555555555555555555555555555555555555555555555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1344 : replayPacked (-1024) 1032 ((ops.drop 1312).take 32) output1312 = some (output1344,1181) := by decide
theorem segment1344 : silentSegment machine (toConfig (-1024) 1032 output1312) (toConfig (-1024) 1032 output1344) 1181 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1312).take 32) output1312 output1344 1181 checked1344).2
theorem blank_start_1344 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1344) 49760 := by
  have h := segAdd machine _ _ _ 48579 1181 blank_start_1312 segment1344
  simpa using h

def output1376 : Packed := ⟨0,-682,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd55555555555555555555555555555555555555555555555555555555500000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1376 : replayPacked (-1024) 1032 ((ops.drop 1344).take 32) output1344 = some (output1376,1554) := by decide
theorem segment1376 : silentSegment machine (toConfig (-1024) 1032 output1344) (toConfig (-1024) 1032 output1376) 1554 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1344).take 32) output1344 output1376 1554 checked1376).2
theorem blank_start_1376 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1376) 51314 := by
  have h := segAdd machine _ _ _ 49760 1554 blank_start_1344 segment1376
  simpa using h

def output1408 : Packed := ⟨0,-697,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1408 : replayPacked (-1024) 1032 ((ops.drop 1376).take 32) output1376 = some (output1408,1493) := by decide
theorem segment1408 : silentSegment machine (toConfig (-1024) 1032 output1376) (toConfig (-1024) 1032 output1408) 1493 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1376).take 32) output1376 output1408 1493 checked1408).2
theorem blank_start_1408 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1408) 52807 := by
  have h := segAdd machine _ _ _ 51314 1493 blank_start_1376 segment1408
  simpa using h

def output1440 : Packed := ⟨2,-713,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5555555555555555555555555555555555555555555555555555555555555555555555c00000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1440 : replayPacked (-1024) 1032 ((ops.drop 1408).take 32) output1408 = some (output1440,1638) := by decide
theorem segment1440 : silentSegment machine (toConfig (-1024) 1032 output1408) (toConfig (-1024) 1032 output1440) 1638 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1408).take 32) output1408 output1440 1638 checked1440).2
theorem blank_start_1440 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1440) 54445 := by
  have h := segAdd machine _ _ _ 52807 1638 blank_start_1408 segment1440
  simpa using h

def output1472 : Packed := ⟨4,-423,0xefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1472 : replayPacked (-1024) 1032 ((ops.drop 1440).take 32) output1440 = some (output1472,2086) := by decide
theorem segment1472 : silentSegment machine (toConfig (-1024) 1032 output1440) (toConfig (-1024) 1032 output1472) 2086 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1440).take 32) output1440 output1472 2086 checked1472).2
theorem blank_start_1472 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1472) 56531 := by
  have h := segAdd machine _ _ _ 54445 2086 blank_start_1440 segment1472
  simpa using h

def output1504 : Packed := ⟨2,-412,0xefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff555555555555555555555555555555555555555555555555555555555555555555555555555555555550000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1504 : replayPacked (-1024) 1032 ((ops.drop 1472).take 32) output1472 = some (output1504,1949) := by decide
theorem segment1504 : silentSegment machine (toConfig (-1024) 1032 output1472) (toConfig (-1024) 1032 output1504) 1949 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1472).take 32) output1472 output1504 1949 checked1504).2
theorem blank_start_1504 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1504) 58480 := by
  have h := segAdd machine _ _ _ 56531 1949 blank_start_1472 segment1504
  simpa using h

def output1536 : Packed := ⟨0,-762,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1536 : replayPacked (-1024) 1032 ((ops.drop 1504).take 32) output1504 = some (output1536,2450) := by decide
theorem segment1536 : silentSegment machine (toConfig (-1024) 1032 output1504) (toConfig (-1024) 1032 output1536) 2450 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1504).take 32) output1504 output1536 2450 checked1536).2
theorem blank_start_1536 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1536) 60930 := by
  have h := segAdd machine _ _ _ 58480 2450 blank_start_1504 segment1536
  simpa using h
end Shared.Beeping.NPcoNP.Bootstrap284PackedContinue1536

#print axioms Shared.Beeping.NPcoNP.Bootstrap284PackedContinue1536.blank_start_1536
