import Shared.Beeping.NPcoNP.Bootstrap284BulkContinue2560
import Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
import Shared.Beeping.NPcoNP.Bootstrap284BulkReplay

/-! Generated continuation; each asserted block requires Lean checking. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284BulkContinue2816
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284PackedScans
open Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
open Shared.Beeping.NPcoNP.Bootstrap284TraceData
open Shared.Beeping.NPcoNP.Bootstrap284BulkContinue2560
open Shared.Beeping.NPcoNP.Bootstrap284BulkReplay
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def startConfig : Packed := extendLeft 0 output2560
theorem start_segment : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 startConfig) 218525 := by
  have h : toConfig (-2048) 2056 startConfig=toConfig (-2048) 2056 output2560 := by
    simpa [startConfig] using toConfig_extendLeft (-2048) 2056 0 output2560
  rw [h]
  exact blank_start_2560

def output2592 : Packed := ⟨4,-87,0xefffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2592 : replayBulk (-2048) 2056 ((ops.drop 2560).take 32) startConfig = some (output2592,8358) := by decide
theorem segment2592 : silentSegment machine (toConfig (-2048) 2056 startConfig) (toConfig (-2048) 2056 output2592) 8358 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2560).take 32) startConfig output2592 8358 checked2592).2
theorem blank_start_2592 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2592) 226883 := by
  have h := segAdd machine _ _ _ 218525 8358 start_segment segment2592
  simpa using h

def output2624 : Packed := ⟨2,-76,0xefffffffffffffffffff5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2624 : replayBulk (-2048) 2056 ((ops.drop 2592).take 32) output2592 = some (output2624,7325) := by decide
theorem segment2624 : silentSegment machine (toConfig (-2048) 2056 output2592) (toConfig (-2048) 2056 output2624) 7325 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2592).take 32) output2592 output2624 7325 checked2624).2
theorem blank_start_2624 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2624) 234208 := by
  have h := segAdd machine _ _ _ 226883 7325 blank_start_2592 segment2624
  simpa using h

def output2656 : Packed := ⟨0,-1322,0xeffffffffffffffffd555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2656 : replayBulk (-2048) 2056 ((ops.drop 2624).take 32) output2624 = some (output2656,8722) := by decide
theorem segment2656 : silentSegment machine (toConfig (-2048) 2056 output2624) (toConfig (-2048) 2056 output2656) 8722 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2624).take 32) output2624 output2656 8722 checked2656).2
theorem blank_start_2656 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2656) 242930 := by
  have h := segAdd machine _ _ _ 234208 8722 blank_start_2624 segment2656
  simpa using h

def output2688 : Packed := ⟨0,-1337,0xeffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2688 : replayBulk (-2048) 2056 ((ops.drop 2656).take 32) output2656 = some (output2688,7637) := by decide
theorem segment2688 : silentSegment machine (toConfig (-2048) 2056 output2656) (toConfig (-2048) 2056 output2688) 7637 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2656).take 32) output2656 output2688 7637 checked2688).2
theorem blank_start_2688 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2688) 250567 := by
  have h := segAdd machine _ _ _ 242930 7637 blank_start_2656 segment2688
  simpa using h

def output2720 : Packed := ⟨2,-1353,0xeffffffffffff55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2720 : replayBulk (-2048) 2056 ((ops.drop 2688).take 32) output2688 = some (output2720,7782) := by decide
theorem segment2720 : silentSegment machine (toConfig (-2048) 2056 output2688) (toConfig (-2048) 2056 output2720) 7782 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2688).take 32) output2688 output2720 7782 checked2720).2
theorem blank_start_2720 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2720) 258349 := by
  have h := segAdd machine _ _ _ 250567 7782 blank_start_2688 segment2720
  simpa using h

def output2752 : Packed := ⟨4,-39,0xefffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2752 : replayBulk (-2048) 2056 ((ops.drop 2720).take 32) output2720 = some (output2752,9254) := by decide
theorem segment2752 : silentSegment machine (toConfig (-2048) 2056 output2720) (toConfig (-2048) 2056 output2752) 9254 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2720).take 32) output2720 output2752 9254 checked2752).2
theorem blank_start_2752 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2752) 267603 := by
  have h := segAdd machine _ _ _ 258349 9254 blank_start_2720 segment2752
  simpa using h

def output2784 : Packed := ⟨2,-28,0xefffffff5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2784 : replayBulk (-2048) 2056 ((ops.drop 2752).take 32) output2752 = some (output2784,8093) := by decide
theorem segment2784 : silentSegment machine (toConfig (-2048) 2056 output2752) (toConfig (-2048) 2056 output2784) 8093 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2752).take 32) output2752 output2784 8093 checked2784).2
theorem blank_start_2784 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2784) 275696 := by
  have h := segAdd machine _ _ _ 267603 8093 blank_start_2752 segment2784
  simpa using h

def output2816 : Packed := ⟨0,-1402,0xeffffd555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked2816 : replayBulk (-2048) 2056 ((ops.drop 2784).take 32) output2784 = some (output2816,9618) := by decide
theorem segment2816 : silentSegment machine (toConfig (-2048) 2056 output2784) (toConfig (-2048) 2056 output2816) 9618 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 2784).take 32) output2784 output2816 9618 checked2816).2
theorem blank_start_2816 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output2816) 285314 := by
  have h := segAdd machine _ _ _ 275696 9618 blank_start_2784 segment2816
  simpa using h
end Shared.Beeping.NPcoNP.Bootstrap284BulkContinue2816

#print axioms Shared.Beeping.NPcoNP.Bootstrap284BulkContinue2816.blank_start_2816
