import Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3072
import Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
import Shared.Beeping.NPcoNP.Bootstrap284BulkReplay

/-! Generated continuation; each asserted block requires Lean checking. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3328
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284PackedScans
open Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
open Shared.Beeping.NPcoNP.Bootstrap284TraceData
open Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3072
open Shared.Beeping.NPcoNP.Bootstrap284BulkReplay
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def startConfig : Packed := extendLeft 0 output3072
theorem start_segment : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 startConfig) 308195 := by
  have h : toConfig (-2048) 2056 startConfig=toConfig (-2048) 2056 output3072 := by
    simpa [startConfig] using toConfig_extendLeft (-2048) 2056 0 output3072
  rw [h]
  exact blank_start_3072

def output3104 : Packed := ⟨0,-1544,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff55555555555555555555555555555555555555555555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3104 : replayBulk (-2048) 2056 ((ops.drop 3072).take 32) startConfig = some (output3104,1013) := by decide
theorem segment3104 : silentSegment machine (toConfig (-2048) 2056 startConfig) (toConfig (-2048) 2056 output3104) 1013 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3072).take 32) startConfig output3104 1013 checked3104).2
theorem blank_start_3104 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3104) 309208 := by
  have h := segAdd machine _ _ _ 308195 1013 start_segment segment3104
  simpa using h

def output3136 : Packed := ⟨2,-1560,0xf7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3136 : replayBulk (-2048) 2056 ((ops.drop 3104).take 32) output3104 = some (output3136,1158) := by decide
theorem segment3136 : silentSegment machine (toConfig (-2048) 2056 output3104) (toConfig (-2048) 2056 output3136) 1158 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3104).take 32) output3104 output3136 1158 checked3136).2
theorem blank_start_3136 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3136) 310366 := by
  have h := segAdd machine _ _ _ 309208 1158 blank_start_3104 segment3136
  simpa using h

def output3168 : Packed := ⟨4,-1350,0xf7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd555555555555555555555555555555555555555555555555555555550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3168 : replayBulk (-2048) 2056 ((ops.drop 3136).take 32) output3136 = some (output3168,1526) := by decide
theorem segment3168 : silentSegment machine (toConfig (-2048) 2056 output3136) (toConfig (-2048) 2056 output3168) 1526 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3136).take 32) output3136 output3168 1526 checked3168).2
theorem blank_start_3168 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3168) 311892 := by
  have h := segAdd machine _ _ _ 310366 1526 blank_start_3136 segment3168
  simpa using h

def output3200 : Packed := ⟨2,-1339,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3200 : replayBulk (-2048) 2056 ((ops.drop 3168).take 32) output3168 = some (output3200,1469) := by decide
theorem segment3200 : silentSegment machine (toConfig (-2048) 2056 output3168) (toConfig (-2048) 2056 output3200) 1469 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3168).take 32) output3168 output3200 1469 checked3200).2
theorem blank_start_3200 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3200) 313361 := by
  have h := segAdd machine _ _ _ 311892 1469 blank_start_3168 segment3200
  simpa using h

def output3232 : Packed := ⟨0,-1609,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3232 : replayBulk (-2048) 2056 ((ops.drop 3200).take 32) output3200 = some (output3232,1890) := by decide
theorem segment3232 : silentSegment machine (toConfig (-2048) 2056 output3200) (toConfig (-2048) 2056 output3232) 1890 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3200).take 32) output3200 output3232 1890 checked3232).2
theorem blank_start_3232 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3232) 315251 := by
  have h := segAdd machine _ _ _ 313361 1890 blank_start_3200 segment3232
  simpa using h

def output3264 : Packed := ⟨0,-1624,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff55555555555555555555555555555555555555555555555555555555555555555555555555550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3264 : replayBulk (-2048) 2056 ((ops.drop 3232).take 32) output3232 = some (output3264,1781) := by decide
theorem segment3264 : silentSegment machine (toConfig (-2048) 2056 output3232) (toConfig (-2048) 2056 output3264) 1781 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3232).take 32) output3232 output3264 1781 checked3264).2
theorem blank_start_3264 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3264) 317032 := by
  have h := segAdd machine _ _ _ 315251 1781 blank_start_3232 segment3264
  simpa using h

def output3296 : Packed := ⟨2,-1640,0xf7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3296 : replayBulk (-2048) 2056 ((ops.drop 3264).take 32) output3264 = some (output3296,1926) := by decide
theorem segment3296 : silentSegment machine (toConfig (-2048) 2056 output3264) (toConfig (-2048) 2056 output3296) 1926 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3264).take 32) output3264 output3296 1926 checked3296).2
theorem blank_start_3296 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3296) 318958 := by
  have h := segAdd machine _ _ _ 317032 1926 blank_start_3264 segment3296
  simpa using h

def output3328 : Packed := ⟨4,-1302,0xf7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd555555555555555555555555555555555555555555555555555555555555555555555555555555555555555500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3328 : replayBulk (-2048) 2056 ((ops.drop 3296).take 32) output3296 = some (output3328,2422) := by decide
theorem segment3328 : silentSegment machine (toConfig (-2048) 2056 output3296) (toConfig (-2048) 2056 output3328) 2422 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3296).take 32) output3296 output3328 2422 checked3328).2
theorem blank_start_3328 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3328) 321380 := by
  have h := segAdd machine _ _ _ 318958 2422 blank_start_3296 segment3328
  simpa using h
end Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3328

#print axioms Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3328.blank_start_3328
