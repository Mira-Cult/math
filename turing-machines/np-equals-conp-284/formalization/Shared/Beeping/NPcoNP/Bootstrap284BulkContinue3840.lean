import Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3584
import Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
import Shared.Beeping.NPcoNP.Bootstrap284BulkReplay

/-! Generated continuation; each asserted block requires Lean checking. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3840
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284PackedScans
open Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
open Shared.Beeping.NPcoNP.Bootstrap284TraceData
open Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3584
open Shared.Beeping.NPcoNP.Bootstrap284BulkReplay
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def startConfig : Packed := extendLeft 0 output3584
theorem start_segment : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 startConfig) 344968 := by
  have h : toConfig (-2048) 2056 startConfig=toConfig (-2048) 2056 output3584 := by
    simpa [startConfig] using toConfig_extendLeft (-2048) 2056 0 output3584
  rw [h]
  exact blank_start_3584

def output3616 : Packed := ⟨2,-1800,0xf7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab80000000000000000000000000000000000000000000000000000000000000⟩
theorem checked3616 : replayBulk (-2048) 2056 ((ops.drop 3584).take 32) startConfig = some (output3616,3462) := by decide
theorem segment3616 : silentSegment machine (toConfig (-2048) 2056 startConfig) (toConfig (-2048) 2056 output3616) 3462 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3584).take 32) startConfig output3616 3462 checked3616).2
theorem blank_start_3616 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3616) 348430 := by
  have h := segAdd machine _ _ _ 344968 3462 start_segment segment3616
  simpa using h

def output3648 : Packed := ⟨4,-1206,0xf7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555550000000000000000000000000000000000000000000000000000000000⟩
theorem checked3648 : replayBulk (-2048) 2056 ((ops.drop 3616).take 32) output3616 = some (output3648,4214) := by decide
theorem segment3648 : silentSegment machine (toConfig (-2048) 2056 output3616) (toConfig (-2048) 2056 output3648) 4214 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3616).take 32) output3616 output3648 4214 checked3648).2
theorem blank_start_3648 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3648) 352644 := by
  have h := segAdd machine _ _ _ 348430 4214 blank_start_3616 segment3648
  simpa using h

def output3680 : Packed := ⟨2,-1195,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000⟩
theorem checked3680 : replayBulk (-2048) 2056 ((ops.drop 3648).take 32) output3648 = some (output3680,3773) := by decide
theorem segment3680 : silentSegment machine (toConfig (-2048) 2056 output3648) (toConfig (-2048) 2056 output3680) 3773 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3648).take 32) output3648 output3680 3773 checked3680).2
theorem blank_start_3680 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3680) 356417 := by
  have h := segAdd machine _ _ _ 352644 3773 blank_start_3648 segment3680
  simpa using h

def output3712 : Packed := ⟨0,-1849,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000000000000000000000⟩
theorem checked3712 : replayBulk (-2048) 2056 ((ops.drop 3680).take 32) output3680 = some (output3712,4578) := by decide
theorem segment3712 : silentSegment machine (toConfig (-2048) 2056 output3680) (toConfig (-2048) 2056 output3712) 4578 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3680).take 32) output3680 output3712 4578 checked3712).2
theorem blank_start_3712 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3712) 360995 := by
  have h := segAdd machine _ _ _ 356417 4578 blank_start_3680 segment3712
  simpa using h

def output3744 : Packed := ⟨0,-1864,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555550000000000000000000000000000000000000000000000⟩
theorem checked3744 : replayBulk (-2048) 2056 ((ops.drop 3712).take 32) output3712 = some (output3744,4085) := by decide
theorem segment3744 : silentSegment machine (toConfig (-2048) 2056 output3712) (toConfig (-2048) 2056 output3744) 4085 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3712).take 32) output3712 output3744 4085 checked3744).2
theorem blank_start_3744 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3744) 365080 := by
  have h := segAdd machine _ _ _ 360995 4085 blank_start_3712 segment3744
  simpa using h

def output3776 : Packed := ⟨2,-1880,0xf7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab800000000000000000000000000000000000000000⟩
theorem checked3776 : replayBulk (-2048) 2056 ((ops.drop 3744).take 32) output3744 = some (output3776,4230) := by decide
theorem segment3776 : silentSegment machine (toConfig (-2048) 2056 output3744) (toConfig (-2048) 2056 output3776) 4230 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3744).take 32) output3744 output3776 4230 checked3776).2
theorem blank_start_3776 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3776) 369310 := by
  have h := segAdd machine _ _ _ 365080 4230 blank_start_3744 segment3776
  simpa using h

def output3808 : Packed := ⟨4,-1158,0xf7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555500000000000000000000000000000000000000⟩
theorem checked3808 : replayBulk (-2048) 2056 ((ops.drop 3776).take 32) output3776 = some (output3808,5110) := by decide
theorem segment3808 : silentSegment machine (toConfig (-2048) 2056 output3776) (toConfig (-2048) 2056 output3808) 5110 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3776).take 32) output3776 output3808 5110 checked3808).2
theorem blank_start_3808 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3808) 374420 := by
  have h := segAdd machine _ _ _ 369310 5110 blank_start_3776 segment3808
  simpa using h

def output3840 : Packed := ⟨2,-1147,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000000000000000000000⟩
theorem checked3840 : replayBulk (-2048) 2056 ((ops.drop 3808).take 32) output3808 = some (output3840,4541) := by decide
theorem segment3840 : silentSegment machine (toConfig (-2048) 2056 output3808) (toConfig (-2048) 2056 output3840) 4541 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3808).take 32) output3808 output3840 4541 checked3840).2
theorem blank_start_3840 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3840) 378961 := by
  have h := segAdd machine _ _ _ 374420 4541 blank_start_3808 segment3840
  simpa using h
end Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3840

#print axioms Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3840.blank_start_3840
