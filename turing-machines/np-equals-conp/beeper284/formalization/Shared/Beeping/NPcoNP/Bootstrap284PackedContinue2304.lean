import Shared.Beeping.NPcoNP.Bootstrap284PackedContinue2048
import Shared.Beeping.NPcoNP.Bootstrap284PackedRebase

/-! Generated continuation; each asserted block requires Lean checking. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284PackedContinue2304
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284PackedScans
open Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
open Shared.Beeping.NPcoNP.Bootstrap284TraceData
open Shared.Beeping.NPcoNP.Bootstrap284PackedContinue2048
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def startConfig : Packed := extendLeft 1024 output2048
theorem start_segment : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 startConfig) 118919 := by
  have h : toConfig (-2048) 2056 startConfig=toConfig (-1024) 1032 output2048 := by
    simpa [startConfig] using toConfig_extendLeft (-1024) 1032 1024 output2048
  rw [h]
  exact blank_start_2048

def output2080 : Packed := ⟨2,-1033,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2080 : replayPacked (-2048) 2056 ((ops.drop 2048).take 32) startConfig = some (output2080,4710) := by decide
theorem segment2080 : silentSegment machine (toConfig (-2048) 2056 startConfig) (toConfig (-2048) 2056 output2080) 4710 :=
  (replayPacked_sound (-2048) 2056 ((ops.drop 2048).take 32) startConfig output2080 4710 checked2080).2
theorem blank_start_2080 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2080) 123629 := by
  have h := segAdd machine _ _ _ 118919 4710 start_segment segment2080
  simpa using h

def output2112 : Packed := ⟨4,-231,0xefffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2112 : replayPacked (-2048) 2056 ((ops.drop 2080).take 32) output2080 = some (output2112,5670) := by decide
theorem segment2112 : silentSegment machine (toConfig (-2048) 2056 output2080) (toConfig (-2048) 2056 output2112) 5670 :=
  (replayPacked_sound (-2048) 2056 ((ops.drop 2080).take 32) output2080 output2112 5670 checked2112).2
theorem blank_start_2112 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2112) 129299 := by
  have h := segAdd machine _ _ _ 123629 5670 blank_start_2080 segment2112
  simpa using h

def output2144 : Packed := ⟨2,-220,0xefffffffffffffffffffffffffffffffffffffffffffffffffffffff5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2144 : replayPacked (-2048) 2056 ((ops.drop 2112).take 32) output2112 = some (output2144,5021) := by decide
theorem segment2144 : silentSegment machine (toConfig (-2048) 2056 output2112) (toConfig (-2048) 2056 output2144) 5021 :=
  (replayPacked_sound (-2048) 2056 ((ops.drop 2112).take 32) output2112 output2144 5021 checked2144).2
theorem blank_start_2144 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2144) 134320 := by
  have h := segAdd machine _ _ _ 129299 5021 blank_start_2112 segment2144
  simpa using h

def output2176 : Packed := ⟨0,-1082,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffd555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2176 : replayPacked (-2048) 2056 ((ops.drop 2144).take 32) output2144 = some (output2176,6034) := by decide
theorem segment2176 : silentSegment machine (toConfig (-2048) 2056 output2144) (toConfig (-2048) 2056 output2176) 6034 :=
  (replayPacked_sound (-2048) 2056 ((ops.drop 2144).take 32) output2144 output2176 6034 checked2176).2
theorem blank_start_2176 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2176) 140354 := by
  have h := segAdd machine _ _ _ 134320 6034 blank_start_2144 segment2176
  simpa using h

def output2208 : Packed := ⟨0,-1097,0xeffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2208 : replayPacked (-2048) 2056 ((ops.drop 2176).take 32) output2176 = some (output2208,5333) := by decide
theorem segment2208 : silentSegment machine (toConfig (-2048) 2056 output2176) (toConfig (-2048) 2056 output2208) 5333 :=
  (replayPacked_sound (-2048) 2056 ((ops.drop 2176).take 32) output2176 output2208 5333 checked2208).2
theorem blank_start_2208 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2208) 145687 := by
  have h := segAdd machine _ _ _ 140354 5333 blank_start_2176 segment2208
  simpa using h

def output2240 : Packed := ⟨2,-1113,0xeffffffffffffffffffffffffffffffffffffffffffffffff55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2240 : replayPacked (-2048) 2056 ((ops.drop 2208).take 32) output2208 = some (output2240,5478) := by decide
theorem segment2240 : silentSegment machine (toConfig (-2048) 2056 output2208) (toConfig (-2048) 2056 output2240) 5478 :=
  (replayPacked_sound (-2048) 2056 ((ops.drop 2208).take 32) output2208 output2240 5478 checked2240).2
theorem blank_start_2240 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2240) 151165 := by
  have h := segAdd machine _ _ _ 145687 5478 blank_start_2208 segment2240
  simpa using h

def output2272 : Packed := ⟨4,-183,0xefffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2272 : replayPacked (-2048) 2056 ((ops.drop 2240).take 32) output2240 = some (output2272,6566) := by decide
theorem segment2272 : silentSegment machine (toConfig (-2048) 2056 output2240) (toConfig (-2048) 2056 output2272) 6566 :=
  (replayPacked_sound (-2048) 2056 ((ops.drop 2240).take 32) output2240 output2272 6566 checked2272).2
theorem blank_start_2272 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2272) 157731 := by
  have h := segAdd machine _ _ _ 151165 6566 blank_start_2240 segment2272
  simpa using h

def output2304 : Packed := ⟨2,-172,0xefffffffffffffffffffffffffffffffffffffffffff5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2304 : replayPacked (-2048) 2056 ((ops.drop 2272).take 32) output2272 = some (output2304,5789) := by decide
theorem segment2304 : silentSegment machine (toConfig (-2048) 2056 output2272) (toConfig (-2048) 2056 output2304) 5789 :=
  (replayPacked_sound (-2048) 2056 ((ops.drop 2272).take 32) output2272 output2304 5789 checked2304).2
theorem blank_start_2304 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2304) 163520 := by
  have h := segAdd machine _ _ _ 157731 5789 blank_start_2272 segment2304
  simpa using h
end Shared.Beeping.NPcoNP.Bootstrap284PackedContinue2304

#print axioms Shared.Beeping.NPcoNP.Bootstrap284PackedContinue2304.blank_start_2304
