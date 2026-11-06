import Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3840
import Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
import Shared.Beeping.NPcoNP.Bootstrap284BulkReplay

/-! Generated continuation; each asserted block requires Lean checking. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284BulkContinue4096
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284PackedScans
open Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
open Shared.Beeping.NPcoNP.Bootstrap284TraceData
open Shared.Beeping.NPcoNP.Bootstrap284BulkContinue3840
open Shared.Beeping.NPcoNP.Bootstrap284BulkReplay
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def startConfig : Packed := extendLeft 0 output3840
theorem start_segment : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 startConfig) 378961 := by
  have h : toConfig (-2048) 2056 startConfig=toConfig (-2048) 2056 output3840 := by
    simpa [startConfig] using toConfig_extendLeft (-2048) 2056 0 output3840
  rw [h]
  exact blank_start_3840

def output3872 : Packed := ⟨0,-1929,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000⟩
theorem checked3872 : replayBulk (-2048) 2056 ((ops.drop 3840).take 32) startConfig = some (output3872,5474) := by decide
theorem segment3872 : silentSegment machine (toConfig (-2048) 2056 startConfig) (toConfig (-2048) 2056 output3872) 5474 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3840).take 32) startConfig output3872 5474 checked3872).2
theorem blank_start_3872 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3872) 384435 := by
  have h := segAdd machine _ _ _ 378961 5474 start_segment segment3872
  simpa using h

def output3904 : Packed := ⟨0,-1944,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555500000000000000000000000000⟩
theorem checked3904 : replayBulk (-2048) 2056 ((ops.drop 3872).take 32) output3872 = some (output3904,4853) := by decide
theorem segment3904 : silentSegment machine (toConfig (-2048) 2056 output3872) (toConfig (-2048) 2056 output3904) 4853 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3872).take 32) output3872 output3904 4853 checked3904).2
theorem blank_start_3904 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3904) 389288 := by
  have h := segAdd machine _ _ _ 384435 4853 blank_start_3872 segment3904
  simpa using h

def output3936 : Packed := ⟨2,-1960,0xf7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab8000000000000000000000⟩
theorem checked3936 : replayBulk (-2048) 2056 ((ops.drop 3904).take 32) output3904 = some (output3936,4998) := by decide
theorem segment3936 : silentSegment machine (toConfig (-2048) 2056 output3904) (toConfig (-2048) 2056 output3936) 4998 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3904).take 32) output3904 output3936 4998 checked3936).2
theorem blank_start_3936 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3936) 394286 := by
  have h := segAdd machine _ _ _ 389288 4998 blank_start_3904 segment3936
  simpa using h

def output3968 : Packed := ⟨4,-1110,0xf7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555000000000000000000⟩
theorem checked3968 : replayBulk (-2048) 2056 ((ops.drop 3936).take 32) output3936 = some (output3968,6006) := by decide
theorem segment3968 : silentSegment machine (toConfig (-2048) 2056 output3936) (toConfig (-2048) 2056 output3968) 6006 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3936).take 32) output3936 output3968 6006 checked3968).2
theorem blank_start_3968 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output3968) 400292 := by
  have h := segAdd machine _ _ _ 394286 6006 blank_start_3936 segment3968
  simpa using h

def output4000 : Packed := ⟨2,-1099,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000⟩
theorem checked4000 : replayBulk (-2048) 2056 ((ops.drop 3968).take 32) output3968 = some (output4000,5309) := by decide
theorem segment4000 : silentSegment machine (toConfig (-2048) 2056 output3968) (toConfig (-2048) 2056 output4000) 5309 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 3968).take 32) output3968 output4000 5309 checked4000).2
theorem blank_start_4000 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output4000) 405601 := by
  have h := segAdd machine _ _ _ 400292 5309 blank_start_3968 segment4000
  simpa using h

def output4032 : Packed := ⟨0,-2009,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000⟩
theorem checked4032 : replayBulk (-2048) 2056 ((ops.drop 4000).take 32) output4000 = some (output4032,6370) := by decide
theorem segment4032 : silentSegment machine (toConfig (-2048) 2056 output4000) (toConfig (-2048) 2056 output4032) 6370 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 4000).take 32) output4000 output4032 6370 checked4032).2
theorem blank_start_4032 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output4032) 411971 := by
  have h := segAdd machine _ _ _ 405601 6370 blank_start_4000 segment4032
  simpa using h

def output4064 : Packed := ⟨0,-2024,0xf7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555000000⟩
theorem checked4064 : replayBulk (-2048) 2056 ((ops.drop 4032).take 32) output4032 = some (output4064,5621) := by decide
theorem segment4064 : silentSegment machine (toConfig (-2048) 2056 output4032) (toConfig (-2048) 2056 output4064) 5621 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 4032).take 32) output4032 output4064 5621 checked4064).2
theorem blank_start_4064 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output4064) 417592 := by
  have h := segAdd machine _ _ _ 411971 5621 blank_start_4032 segment4064
  simpa using h

def output4096 : Packed := ⟨2,-2040,0xf7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab80⟩
theorem checked4096 : replayBulk (-2048) 2056 ((ops.drop 4064).take 32) output4064 = some (output4096,5766) := by decide
theorem segment4096 : silentSegment machine (toConfig (-2048) 2056 output4064) (toConfig (-2048) 2056 output4096) 5766 :=
  (replayBulk_sound (-2048) 2056 ((ops.drop 4064).take 32) output4064 output4096 5766 checked4096).2
theorem blank_start_4096 : silentSegment machine (machine.system.run 0) (toConfig (-2048) 2056 output4096) 423358 := by
  have h := segAdd machine _ _ _ 417592 5766 blank_start_4064 segment4096
  simpa using h
end Shared.Beeping.NPcoNP.Bootstrap284BulkContinue4096

#print axioms Shared.Beeping.NPcoNP.Bootstrap284BulkContinue4096.blank_start_4096
