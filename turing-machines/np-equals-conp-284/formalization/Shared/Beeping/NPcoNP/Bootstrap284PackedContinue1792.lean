import Shared.Beeping.NPcoNP.Bootstrap284PackedContinue1536
import Shared.Beeping.NPcoNP.Bootstrap284PackedRebase

/-! Generated continuation; each asserted block requires Lean checking. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284PackedContinue1792
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284PackedScans
open Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
open Shared.Beeping.NPcoNP.Bootstrap284TraceData
open Shared.Beeping.NPcoNP.Bootstrap284PackedContinue1536
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def startConfig : Packed := extendLeft 0 output1536
theorem start_segment : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 startConfig) 60930 := by
  have h : toConfig (-1024) 1032 startConfig=toConfig (-1024) 1032 output1536 := by
    simpa [startConfig] using toConfig_extendLeft (-1024) 1032 0 output1536
  rw [h]
  exact blank_start_1536

def output1568 : Packed := ⟨0,-777,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000000000000000000000000000000000000000000000000000⟩
theorem checked1568 : replayPacked (-1024) 1032 ((ops.drop 1536).take 32) startConfig = some (output1568,2261) := by decide
theorem segment1568 : silentSegment machine (toConfig (-1024) 1032 startConfig) (toConfig (-1024) 1032 output1568) 2261 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1536).take 32) startConfig output1568 2261 checked1568).2
theorem blank_start_1568 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1568) 63191 := by
  have h := segAdd machine _ _ _ 60930 2261 start_segment segment1568
  simpa using h

def output1600 : Packed := ⟨2,-793,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555c000000000000000000000000000000000000000000000000000000000⟩
theorem checked1600 : replayPacked (-1024) 1032 ((ops.drop 1568).take 32) output1568 = some (output1600,2406) := by decide
theorem segment1600 : silentSegment machine (toConfig (-1024) 1032 output1568) (toConfig (-1024) 1032 output1600) 2406 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1568).take 32) output1568 output1600 2406 checked1600).2
theorem blank_start_1600 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1600) 65597 := by
  have h := segAdd machine _ _ _ 63191 2406 blank_start_1568 segment1600
  simpa using h

def output1632 : Packed := ⟨4,-375,0xefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000000000000000000000000000000000⟩
theorem checked1632 : replayPacked (-1024) 1032 ((ops.drop 1600).take 32) output1600 = some (output1632,2982) := by decide
theorem segment1632 : silentSegment machine (toConfig (-1024) 1032 output1600) (toConfig (-1024) 1032 output1632) 2982 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1600).take 32) output1600 output1632 2982 checked1632).2
theorem blank_start_1632 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1632) 68579 := by
  have h := segAdd machine _ _ _ 65597 2982 blank_start_1600 segment1632
  simpa using h

def output1664 : Packed := ⟨2,-364,0xefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555500000000000000000000000000000000000000000000000000⟩
theorem checked1664 : replayPacked (-1024) 1032 ((ops.drop 1632).take 32) output1632 = some (output1664,2717) := by decide
theorem segment1664 : silentSegment machine (toConfig (-1024) 1032 output1632) (toConfig (-1024) 1032 output1664) 2717 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1632).take 32) output1632 output1664 2717 checked1664).2
theorem blank_start_1664 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1664) 71296 := by
  have h := segAdd machine _ _ _ 68579 2717 blank_start_1632 segment1664
  simpa using h

def output1696 : Packed := ⟨0,-842,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555550000000000000000000000000000000000000000000000⟩
theorem checked1696 : replayPacked (-1024) 1032 ((ops.drop 1664).take 32) output1664 = some (output1696,3346) := by decide
theorem segment1696 : silentSegment machine (toConfig (-1024) 1032 output1664) (toConfig (-1024) 1032 output1696) 3346 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1664).take 32) output1664 output1696 3346 checked1696).2
theorem blank_start_1696 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1696) 74642 := by
  have h := segAdd machine _ _ _ 71296 3346 blank_start_1664 segment1696
  simpa using h

def output1728 : Packed := ⟨0,-857,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000000000000000000000⟩
theorem checked1728 : replayPacked (-1024) 1032 ((ops.drop 1696).take 32) output1696 = some (output1728,3029) := by decide
theorem segment1728 : silentSegment machine (toConfig (-1024) 1032 output1696) (toConfig (-1024) 1032 output1728) 3029 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1696).take 32) output1696 output1728 3029 checked1728).2
theorem blank_start_1728 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1728) 77671 := by
  have h := segAdd machine _ _ _ 74642 3029 blank_start_1696 segment1728
  simpa using h

def output1760 : Packed := ⟨2,-873,0xeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555c0000000000000000000000000000000000000⟩
theorem checked1760 : replayPacked (-1024) 1032 ((ops.drop 1728).take 32) output1728 = some (output1760,3174) := by decide
theorem segment1760 : silentSegment machine (toConfig (-1024) 1032 output1728) (toConfig (-1024) 1032 output1760) 3174 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1728).take 32) output1728 output1760 3174 checked1760).2
theorem blank_start_1760 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1760) 80845 := by
  have h := segAdd machine _ _ _ 77671 3174 blank_start_1728 segment1760
  simpa using h

def output1792 : Packed := ⟨4,-327,0xefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000000000000000000000000000000000⟩
theorem checked1792 : replayPacked (-1024) 1032 ((ops.drop 1760).take 32) output1760 = some (output1792,3878) := by decide
theorem segment1792 : silentSegment machine (toConfig (-1024) 1032 output1760) (toConfig (-1024) 1032 output1792) 3878 :=
  (replayPacked_sound (-1024) 1032 ((ops.drop 1760).take 32) output1760 output1792 3878 checked1792).2
theorem blank_start_1792 : silentSegment machine (machine.system.run 0) (toConfig (-1024) 1032 output1792) 84723 := by
  have h := segAdd machine _ _ _ 80845 3878 blank_start_1760 segment1792
  simpa using h
end Shared.Beeping.NPcoNP.Bootstrap284PackedContinue1792

#print axioms Shared.Beeping.NPcoNP.Bootstrap284PackedContinue1792.blank_start_1792
