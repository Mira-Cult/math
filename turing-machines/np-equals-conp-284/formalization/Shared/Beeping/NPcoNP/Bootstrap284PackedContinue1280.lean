import Shared.Beeping.NPcoNP.Bootstrap284PackedChunks1024
import Shared.Beeping.NPcoNP.Bootstrap284PackedRebase

/-! Generated continuation; each asserted block requires Lean checking. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284PackedContinue1280
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284PackedScans
open Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
open Shared.Beeping.NPcoNP.Bootstrap284TraceData
open Shared.Beeping.NPcoNP.Bootstrap284PackedChunks1024
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def startConfig : Packed := extendLeft 512 output1024
theorem start_segment : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 startConfig) 37052 := by
  have h : toConfig (-1024) 1032 startConfig=toConfig (-512) 520 output1024 := by
    simpa [startConfig] using toConfig_extendLeft (-512) 520 512 output1024
  rw [h]
  exact blank_start_1024

def output1056 : Packed := ⟨4,-8,0xdff55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1056 : replayPacked (-1024) 1032 ((ops.drop 1024).take 32) startConfig = some (output1056,3542) := by decide
theorem segment1056 : silentSegment machine (toConfig (-1024) 1032 startConfig) (toConfig (-1024) 1032 output1056) 3542 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1024).take 32) startConfig output1056 3542 checked1056).2
theorem blank_start_1056 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1056) 40594 := by
  have h := segAdd machine _ _ _ 37052 3542 start_segment segment1056
  simpa using h

def output1088 : Packed := ⟨0,-1,0xeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1088 : replayPacked (-1024) 1032 ((ops.drop 1056).take 32) output1056 = some (output1088,3197) := by decide
theorem segment1088 : silentSegment machine (toConfig (-1024) 1032 output1056) (toConfig (-1024) 1032 output1088) 3197 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1056).take 32) output1056 output1088 3197 checked1088).2
theorem blank_start_1088 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1088) 43791 := by
  have h := segAdd machine _ _ _ 40594 3197 blank_start_1056 segment1088
  simpa using h

def output1120 : Packed := ⟨2,-553,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff555555c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1120 : replayPacked (-1024) 1032 ((ops.drop 1088).take 32) output1088 = some (output1120,638) := by decide
theorem segment1120 : silentSegment machine (toConfig (-1024) 1032 output1088) (toConfig (-1024) 1032 output1120) 638 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1088).take 32) output1088 output1120 638 checked1120).2
theorem blank_start_1120 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1120) 44429 := by
  have h := segAdd machine _ _ _ 43791 638 blank_start_1088 segment1120
  simpa using h

def output1152 : Packed := ⟨4,-519,0xefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaa800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1152 : replayPacked (-1024) 1032 ((ops.drop 1120).take 32) output1120 = some (output1152,294) := by decide
theorem segment1152 : silentSegment machine (toConfig (-1024) 1032 output1120) (toConfig (-1024) 1032 output1152) 294 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1120).take 32) output1120 output1152 294 checked1152).2
theorem blank_start_1152 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1152) 44723 := by
  have h := segAdd machine _ _ _ 44429 294 blank_start_1120 segment1152
  simpa using h

def output1184 : Packed := ⟨2,-508,0xefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff555555555555555555500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1184 : replayPacked (-1024) 1032 ((ops.drop 1152).take 32) output1152 = some (output1184,413) := by decide
theorem segment1184 : silentSegment machine (toConfig (-1024) 1032 output1152) (toConfig (-1024) 1032 output1184) 413 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1152).take 32) output1152 output1184 413 checked1184).2
theorem blank_start_1184 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1184) 45136 := by
  have h := segAdd machine _ _ _ 44723 413 blank_start_1152 segment1184
  simpa using h

def output1216 : Packed := ⟨0,-602,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd55555555555555555555555550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1216 : replayPacked (-1024) 1032 ((ops.drop 1184).take 32) output1184 = some (output1216,658) := by decide
theorem segment1216 : silentSegment machine (toConfig (-1024) 1032 output1184) (toConfig (-1024) 1032 output1216) 658 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1184).take 32) output1184 output1216 658 checked1216).2
theorem blank_start_1216 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1216) 45794 := by
  have h := segAdd machine _ _ _ 45136 658 blank_start_1184 segment1216
  simpa using h

def output1248 : Packed := ⟨0,-617,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1248 : replayPacked (-1024) 1032 ((ops.drop 1216).take 32) output1216 = some (output1248,725) := by decide
theorem segment1248 : silentSegment machine (toConfig (-1024) 1032 output1216) (toConfig (-1024) 1032 output1248) 725 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1216).take 32) output1216 output1248 725 checked1248).2
theorem blank_start_1248 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1248) 46519 := by
  have h := segAdd machine _ _ _ 45794 725 blank_start_1216 segment1248
  simpa using h

def output1280 : Packed := ⟨2,-633,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff55555555555555555555555555555555555555c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1280 : replayPacked (-1024) 1032 ((ops.drop 1248).take 32) output1248 = some (output1280,870) := by decide
theorem segment1280 : silentSegment machine (toConfig (-1024) 1032 output1248) (toConfig (-1024) 1032 output1280) 870 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1248).take 32) output1248 output1280 870 checked1280).2
theorem blank_start_1280 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1280) 47389 := by
  have h := segAdd machine _ _ _ 46519 870 blank_start_1248 segment1280
  simpa using h
end Shared.Beeping.NPcoNP.Bootstrap284PackedContinue1280

#print axioms Shared.Beeping.NPcoNP.Bootstrap284PackedContinue1280.blank_start_1280
