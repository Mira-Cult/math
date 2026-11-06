import Shared.Beeping.NPcoNP.Bootstrap284PackedContinue1792
import Shared.Beeping.NPcoNP.Bootstrap284PackedRebase

/-! Generated continuation; each asserted block requires Lean checking. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284PackedContinue2048
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284PackedScans
open Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
open Shared.Beeping.NPcoNP.Bootstrap284TraceData
open Shared.Beeping.NPcoNP.Bootstrap284PackedContinue1792
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def startConfig : Packed := extendLeft 0 output1792
theorem start_segment : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 startConfig) 84723 := by
  have h : toConfig (-1024) 1032 startConfig=toConfig (-1024) 1032 output1792 := by
    simpa [startConfig] using toConfig_extendLeft (-1024) 1032 0 output1792
  rw [h]
  exact blank_start_1792

def output1824 : Packed := ⟨2,-316,0xefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555000000000000000000000000000000⟩
theorem checked1824 : replayPacked (-1024) 1032 ((ops.drop 1792).take 32) startConfig = some (output1824,3485) := by decide
theorem segment1824 : silentSegment machine (toConfig (-1024) 1032 startConfig) (toConfig (-1024) 1032 output1824) 3485 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1792).take 32) startConfig output1824 3485 checked1824).2
theorem blank_start_1824 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1824) 88208 := by
  have h := segAdd machine _ _ _ 84723 3485 start_segment segment1824
  simpa using h

def output1856 : Packed := ⟨0,-922,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555500000000000000000000000000⟩
theorem checked1856 : replayPacked (-1024) 1032 ((ops.drop 1824).take 32) output1824 = some (output1856,4242) := by decide
theorem segment1856 : silentSegment machine (toConfig (-1024) 1032 output1824) (toConfig (-1024) 1032 output1856) 4242 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1824).take 32) output1824 output1856 4242 checked1856).2
theorem blank_start_1856 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1856) 92450 := by
  have h := segAdd machine _ _ _ 88208 4242 blank_start_1824 segment1856
  simpa using h

def output1888 : Packed := ⟨0,-937,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000000000000000000000⟩
theorem checked1888 : replayPacked (-1024) 1032 ((ops.drop 1856).take 32) output1856 = some (output1888,3797) := by decide
theorem segment1888 : silentSegment machine (toConfig (-1024) 1032 output1856) (toConfig (-1024) 1032 output1888) 3797 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1856).take 32) output1856 output1888 3797 checked1888).2
theorem blank_start_1888 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1888) 96247 := by
  have h := segAdd machine _ _ _ 92450 3797 blank_start_1856 segment1888
  simpa using h

def output1920 : Packed := ⟨2,-953,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555c00000000000000000⟩
theorem checked1920 : replayPacked (-1024) 1032 ((ops.drop 1888).take 32) output1888 = some (output1920,3942) := by decide
theorem segment1920 : silentSegment machine (toConfig (-1024) 1032 output1888) (toConfig (-1024) 1032 output1920) 3942 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1888).take 32) output1888 output1920 3942 checked1920).2
theorem blank_start_1920 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1920) 100189 := by
  have h := segAdd machine _ _ _ 96247 3942 blank_start_1888 segment1920
  simpa using h

def output1952 : Packed := ⟨4,-279,0xefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000⟩
theorem checked1952 : replayPacked (-1024) 1032 ((ops.drop 1920).take 32) output1920 = some (output1952,4774) := by decide
theorem segment1952 : silentSegment machine (toConfig (-1024) 1032 output1920) (toConfig (-1024) 1032 output1952) 4774 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1920).take 32) output1920 output1952 4774 checked1952).2
theorem blank_start_1952 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1952) 104963 := by
  have h := segAdd machine _ _ _ 100189 4774 blank_start_1920 segment1952
  simpa using h

def output1984 : Packed := ⟨2,-268,0xefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555550000000000⟩
theorem checked1984 : replayPacked (-1024) 1032 ((ops.drop 1952).take 32) output1952 = some (output1984,4253) := by decide
theorem segment1984 : silentSegment machine (toConfig (-1024) 1032 output1952) (toConfig (-1024) 1032 output1984) 4253 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1952).take 32) output1952 output1984 4253 checked1984).2
theorem blank_start_1984 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1984) 109216 := by
  have h := segAdd machine _ _ _ 104963 4253 blank_start_1952 segment1984
  simpa using h

def output2016 : Packed := ⟨0,-1002,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555000000⟩
theorem checked2016 : replayPacked (-1024) 1032 ((ops.drop 1984).take 32) output1984 = some (output2016,5138) := by decide
theorem segment2016 : silentSegment machine (toConfig (-1024) 1032 output1984) (toConfig (-1024) 1032 output2016) 5138 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1984).take 32) output1984 output2016 5138 checked2016).2
theorem blank_start_2016 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output2016) 114354 := by
  have h := segAdd machine _ _ _ 109216 5138 blank_start_1984 segment2016
  simpa using h

def output2048 : Packed := ⟨0,-1017,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80⟩
theorem checked2048 : replayPacked (-1024) 1032 ((ops.drop 2016).take 32) output2016 = some (output2048,4565) := by decide
theorem segment2048 : silentSegment machine (toConfig (-1024) 1032 output2016) (toConfig (-1024) 1032 output2048) 4565 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 2016).take 32) output2016 output2048 4565 checked2048).2
theorem blank_start_2048 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output2048) 118919 := by
  have h := segAdd machine _ _ _ 114354 4565 blank_start_2016 segment2048
  simpa using h
end Shared.Beeping.NPcoNP.Bootstrap284PackedContinue2048

#print axioms Shared.Beeping.NPcoNP.Bootstrap284PackedContinue2048.blank_start_2048
