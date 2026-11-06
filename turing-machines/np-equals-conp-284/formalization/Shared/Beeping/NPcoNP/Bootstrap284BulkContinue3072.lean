import Shared.Beeping.NPcoNP.Bootstrap284BulkContinue2816
import Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
import Shared.Beeping.NPcoNP.Bootstrap284BulkReplay

/-! Generated continuation; each asserted block requires Lean checking. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3072
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284PackedScans
open Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
open Shared.Beeping.NPcoNP.Bootstrap284TraceData
open Shared.Beeping.NPcoNP.Bootstrap284BulkContinue2816
open Shared.Beeping.NPcoNP.Bootstrap284BulkReplay
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def startConfig : Packed := extendLeft 0 output2816
theorem start_segment : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 startConfig) 285314 := by
  have h : toConfig (-2048) 2056 startConfig=toConfig (-2048) 2056 output2816 := by
    simpa [startConfig] using toConfig_extendLeft (-2048) 2056 0 output2816
  rw [h]
  exact blank_start_2816

def output2848 : Packed := ⟨0,-1417,0xeffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2848 : replayBulk (-2048) 2056 ((ops.drop 2816).take 32) startConfig = some (output2848,8405) := by decide
theorem segment2848 : silentSegment machine (toConfig (-2048) 2056 startConfig) (toConfig (-2048) 2056 output2848) 8405 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2816).take 32) startConfig output2848 8405 checked2848).2
theorem blank_start_2848 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2848) 293719 := by
  have h := segAdd machine _ _ _ 285314 8405 start_segment segment2848
  simpa using h

def output2880 : Packed := ⟨2,-1433,0xe5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2880 : replayBulk (-2048) 2056 ((ops.drop 2848).take 32) output2848 = some (output2880,8550) := by decide
theorem segment2880 : silentSegment machine (toConfig (-2048) 2056 output2848) (toConfig (-2048) 2056 output2880) 8550 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2848).take 32) output2848 output2880 8550 checked2880).2
theorem blank_start_2880 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2880) 302269 := by
  have h := segAdd machine _ _ _ 293719 8550 blank_start_2848 segment2880
  simpa using h

def output2912 : Packed := ⟨0,-1449,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2912 : replayBulk (-2048) 2056 ((ops.drop 2880).take 32) output2880 = some (output2912,2966) := by decide
theorem segment2912 : silentSegment machine (toConfig (-2048) 2056 output2880) (toConfig (-2048) 2056 output2912) 2966 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2880).take 32) output2880 output2912 2966 checked2912).2
theorem blank_start_2912 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2912) 305235 := by
  have h := segAdd machine _ _ _ 302269 2966 blank_start_2880 segment2912
  simpa using h

def output2944 : Packed := ⟨0,-1464,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff55555555555500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2944 : replayBulk (-2048) 2056 ((ops.drop 2912).take 32) output2912 = some (output2944,245) := by decide
theorem segment2944 : silentSegment machine (toConfig (-2048) 2056 output2912) (toConfig (-2048) 2056 output2944) 245 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2912).take 32) output2912 output2944 245 checked2944).2
theorem blank_start_2944 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2944) 305480 := by
  have h := segAdd machine _ _ _ 305235 245 blank_start_2912 segment2944
  simpa using h

def output2976 : Packed := ⟨2,-1480,0xf7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaab8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2976 : replayBulk (-2048) 2056 ((ops.drop 2944).take 32) output2944 = some (output2976,390) := by decide
theorem segment2976 : silentSegment machine (toConfig (-2048) 2056 output2944) (toConfig (-2048) 2056 output2976) 390 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2944).take 32) output2944 output2976 390 checked2976).2
theorem blank_start_2976 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2976) 305870 := by
  have h := segAdd machine _ _ _ 305480 390 blank_start_2944 segment2976
  simpa using h

def output3008 : Packed := ⟨4,-1398,0xf7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd555555555555555555555555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3008 : replayBulk (-2048) 2056 ((ops.drop 2976).take 32) output2976 = some (output3008,630) := by decide
theorem segment3008 : silentSegment machine (toConfig (-2048) 2056 output2976) (toConfig (-2048) 2056 output3008) 630 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2976).take 32) output2976 output3008 630 checked3008).2
theorem blank_start_3008 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3008) 306500 := by
  have h := segAdd machine _ _ _ 305870 630 blank_start_2976 segment3008
  simpa using h

def output3040 : Packed := ⟨2,-1387,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3040 : replayBulk (-2048) 2056 ((ops.drop 3008).take 32) output3008 = some (output3040,701) := by decide
theorem segment3040 : silentSegment machine (toConfig (-2048) 2056 output3008) (toConfig (-2048) 2056 output3040) 701 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3008).take 32) output3008 output3040 701 checked3040).2
theorem blank_start_3040 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3040) 307201 := by
  have h := segAdd machine _ _ _ 306500 701 blank_start_3008 segment3040
  simpa using h

def output3072 : Packed := ⟨0,-1529,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3072 : replayBulk (-2048) 2056 ((ops.drop 3040).take 32) output3040 = some (output3072,994) := by decide
theorem segment3072 : silentSegment machine (toConfig (-2048) 2056 output3040) (toConfig (-2048) 2056 output3072) 994 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3040).take 32) output3040 output3072 994 checked3072).2
theorem blank_start_3072 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3072) 308195 := by
  have h := segAdd machine _ _ _ 307201 994 blank_start_3040 segment3072
  simpa using h
end Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3072

#print axioms Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3072.blank_start_3072
