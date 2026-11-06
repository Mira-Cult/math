import Shared.Beeping.NPcoNP.Bootstrap284PackedScans
import Shared.Beeping.NPcoNP.Bootstrap284TraceData

/-! Generated packed chunk inputs; each assertion requires Lean checking. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284PackedChunks1024
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284PackedScans
open Shared.Beeping.NPcoNP.Bootstrap284TraceData
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def output0 : Packed := ⟨0,0,0⟩
theorem packed_initial : toConfig (-512) 520 output0=machine.system.run 0 := by
  have hz : machine.start=(0 : Fin 284) := Fin.ext machine_starts_zero.1
  have hb : bitSnapshot (-512) 520 0 = (fun _ => false) := by
    funext p
    simp [bitSnapshot]
  change cfg 0 0 (bitSnapshot (-512) 520 0)=machine.initial
  rw [hb]
  simp [Machine.initial,cfg,hz,machine_starts_zero.2.1,machine_starts_zero.2.2]
theorem blank_start_0 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output0) 0 := by
  rw [packed_initial]
  simp [silentSegment,W,WordEventSystem.advance,WordEventSystem.wordFrom]

def output32 : Packed := ⟨0,-14,0x6fd500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked32 : replayPacked (-512) 520 ((ops.drop 0).take 32) output0 = some (output32,70) := by decide
theorem segment32 : silentSegment machine (toConfig (-512) 520 output0) (toConfig (-512) 520 output32) 70 :=
  (replayPacked_sound (-512) 520 ((ops.drop 0).take 32) output0 output32 70 checked32).2
theorem blank_start_32 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output32) 70 := by
  have h := segAdd machine _ _ _ 0 70 blank_start_0 segment32
  simpa using h

def output64 : Packed := ⟨4,-26,0x77fffffd0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked64 : replayPacked (-512) 520 ((ops.drop 32).take 32) output32 = some (output64,146) := by decide
theorem segment64 : silentSegment machine (toConfig (-512) 520 output32) (toConfig (-512) 520 output64) 146 :=
  (replayPacked_sound (-512) 520 ((ops.drop 32).take 32) output32 output64 146 checked64).2
theorem blank_start_64 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output64) 216 := by
  have h := segAdd machine _ _ _ 70 146 blank_start_32 segment64
  simpa using h

def output96 : Packed := ⟨2,-15,0x77ffeaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked96 : replayPacked (-512) 520 ((ops.drop 64).take 32) output64 = some (output96,125) := by decide
theorem segment96 : silentSegment machine (toConfig (-512) 520 output64) (toConfig (-512) 520 output96) 125 :=
  (replayPacked_sound (-512) 520 ((ops.drop 64).take 32) output64 output96 125 checked96).2
theorem blank_start_96 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output96) 341 := by
  have h := segAdd machine _ _ _ 216 125 blank_start_64 segment96
  simpa using h

def output128 : Packed := ⟨0,-61,0x77aaaaaaaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked128 : replayPacked (-512) 520 ((ops.drop 96).take 32) output96 = some (output128,322) := by decide
theorem segment128 : silentSegment machine (toConfig (-512) 520 output96) (toConfig (-512) 520 output128) 322 :=
  (replayPacked_sound (-512) 520 ((ops.drop 96).take 32) output96 output128 322 checked128).2
theorem blank_start_128 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output128) 663 := by
  have h := segAdd machine _ _ _ 341 322 blank_start_96 segment128
  simpa using h

def output160 : Packed := ⟨4,-73,0xbffffffffffffffffffa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked160 : replayPacked (-512) 520 ((ops.drop 128).take 32) output128 = some (output160,442) := by decide
theorem segment160 : silentSegment machine (toConfig (-512) 520 output128) (toConfig (-512) 520 output160) 442 :=
  (replayPacked_sound (-512) 520 ((ops.drop 128).take 32) output128 output160 442 checked160).2
theorem blank_start_160 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output160) 1105 := by
  have h := segAdd machine _ _ _ 663 442 blank_start_128 segment160
  simpa using h

def output192 : Packed := ⟨2,-62,0xbfffffffffffffffd5555554000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked192 : replayPacked (-512) 520 ((ops.drop 160).take 32) output160 = some (output192,125) := by decide
theorem segment192 : silentSegment machine (toConfig (-512) 520 output160) (toConfig (-512) 520 output192) 125 :=
  (replayPacked_sound (-512) 520 ((ops.drop 160).take 32) output160 output192 125 checked192).2
theorem blank_start_192 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output192) 1230 := by
  have h := segAdd machine _ _ _ 1105 125 blank_start_160 segment192
  simpa using h

def output224 : Packed := ⟨0,-108,0xbfffffffffffff5555555555555400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked224 : replayPacked (-512) 520 ((ops.drop 192).take 32) output192 = some (output224,322) := by decide
theorem segment224 : silentSegment machine (toConfig (-512) 520 output192) (toConfig (-512) 520 output224) 322 :=
  (replayPacked_sound (-512) 520 ((ops.drop 192).take 32) output192 output224 322 checked224).2
theorem blank_start_224 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output224) 1552 := by
  have h := segAdd machine _ _ _ 1230 322 blank_start_192 segment224
  simpa using h

def output256 : Packed := ⟨0,-123,0xbffffffffffeaaaaaaaaaaaaaaaaaaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked256 : replayPacked (-512) 520 ((ops.drop 224).take 32) output224 = some (output256,437) := by decide
theorem segment256 : silentSegment machine (toConfig (-512) 520 output224) (toConfig (-512) 520 output256) 437 :=
  (replayPacked_sound (-512) 520 ((ops.drop 224).take 32) output224 output256 437 checked256).2
theorem blank_start_256 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output256) 1989 := by
  have h := segAdd machine _ _ _ 1552 437 blank_start_224 segment256
  simpa using h

def output288 : Packed := ⟨2,-139,0xbffffffffd55555555555555555555555557000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked288 : replayPacked (-512) 520 ((ops.drop 256).take 32) output256 = some (output288,582) := by decide
theorem segment288 : silentSegment machine (toConfig (-512) 520 output256) (toConfig (-512) 520 output288) 582 :=
  (replayPacked_sound (-512) 520 ((ops.drop 256).take 32) output256 output288 582 checked288).2
theorem blank_start_288 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output288) 2571 := by
  have h := segAdd machine _ _ _ 1989 582 blank_start_256 segment288
  simpa using h

def output320 : Packed := ⟨4,-25,0xbffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked320 : replayPacked (-512) 520 ((ops.drop 288).take 32) output288 = some (output320,854) := by decide
theorem segment320 : silentSegment machine (toConfig (-512) 520 output288) (toConfig (-512) 520 output320) 854 :=
  (replayPacked_sound (-512) 520 ((ops.drop 288).take 32) output288 output320 854 checked320).2
theorem blank_start_320 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output320) 3425 := by
  have h := segAdd machine _ _ _ 2571 854 blank_start_288 segment320
  simpa using h

def output352 : Packed := ⟨2,-14,0xbfffd5555555555555555555555555555555555555540000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked352 : replayPacked (-512) 520 ((ops.drop 320).take 32) output320 = some (output352,893) := by decide
theorem segment352 : silentSegment machine (toConfig (-512) 520 output320) (toConfig (-512) 520 output352) 893 :=
  (replayPacked_sound (-512) 520 ((ops.drop 320).take 32) output320 output352 893 checked352).2
theorem blank_start_352 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output352) 4318 := by
  have h := segAdd machine _ _ _ 3425 893 blank_start_320 segment352
  simpa using h

def output384 : Packed := ⟨0,-188,0xbf5555555555555555555555555555555555555555555554000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked384 : replayPacked (-512) 520 ((ops.drop 352).take 32) output352 = some (output384,1218) := by decide
theorem segment384 : silentSegment machine (toConfig (-512) 520 output352) (toConfig (-512) 520 output384) 1218 :=
  (replayPacked_sound (-512) 520 ((ops.drop 352).take 32) output352 output384 1218 checked384).2
theorem blank_start_384 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output384) 5536 := by
  have h := segAdd machine _ _ _ 4318 1218 blank_start_352 segment384
  simpa using h

def output416 : Packed := ⟨4,-200,0xdffffffffffffffffffffffffffffffffffffffffffffffffff400000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked416 : replayPacked (-512) 520 ((ops.drop 384).take 32) output384 = some (output416,1202) := by decide
theorem segment416 : silentSegment machine (toConfig (-512) 520 output384) (toConfig (-512) 520 output416) 1202 :=
  (replayPacked_sound (-512) 520 ((ops.drop 384).take 32) output384 output416 1202 checked416).2
theorem blank_start_416 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output416) 6738 := by
  have h := segAdd machine _ _ _ 5536 1202 blank_start_384 segment416
  simpa using h

def output448 : Packed := ⟨2,-189,0xdfffffffffffffffffffffffffffffffffffffffffffffffaaaaaaa80000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked448 : replayPacked (-512) 520 ((ops.drop 416).take 32) output416 = some (output448,125) := by decide
theorem segment448 : silentSegment machine (toConfig (-512) 520 output416) (toConfig (-512) 520 output448) 125 :=
  (replayPacked_sound (-512) 520 ((ops.drop 416).take 32) output416 output448 125 checked448).2
theorem blank_start_448 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output448) 6863 := by
  have h := segAdd machine _ _ _ 6738 125 blank_start_416 segment448
  simpa using h

def output480 : Packed := ⟨0,-235,0xdffffffffffffffffffffffffffffffffffffffffffffeaaaaaaaaaaaaa8000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked480 : replayPacked (-512) 520 ((ops.drop 448).take 32) output448 = some (output480,322) := by decide
theorem segment480 : silentSegment machine (toConfig (-512) 520 output448) (toConfig (-512) 520 output480) 322 :=
  (replayPacked_sound (-512) 520 ((ops.drop 448).take 32) output448 output480 322 checked480).2
theorem blank_start_480 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output480) 7185 := by
  have h := segAdd machine _ _ _ 6863 322 blank_start_448 segment480
  simpa using h

def output512 : Packed := ⟨0,-250,0xdffffffffffffffffffffffffffffffffffffffffffd5555555555555555555400000000000000000000000000000000000000000000000000000000000000000⟩
theorem checked512 : replayPacked (-512) 520 ((ops.drop 480).take 32) output480 = some (output512,437) := by decide
theorem segment512 : silentSegment machine (toConfig (-512) 520 output480) (toConfig (-512) 520 output512) 437 :=
  (replayPacked_sound (-512) 520 ((ops.drop 480).take 32) output480 output512 437 checked512).2
theorem blank_start_512 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output512) 7622 := by
  have h := segAdd machine _ _ _ 7185 437 blank_start_480 segment512
  simpa using h

def output544 : Packed := ⟨2,-266,0xdffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaae0000000000000000000000000000000000000000000000000000000000000⟩
theorem checked544 : replayPacked (-512) 520 ((ops.drop 512).take 32) output512 = some (output544,582) := by decide
theorem segment544 : silentSegment machine (toConfig (-512) 520 output512) (toConfig (-512) 520 output544) 582 :=
  (replayPacked_sound (-512) 520 ((ops.drop 512).take 32) output512 output544 582 checked544).2
theorem blank_start_544 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output544) 8204 := by
  have h := segAdd machine _ _ _ 7622 582 blank_start_512 segment544
  simpa using h

def output576 : Packed := ⟨4,-152,0xdffffffffffffffffffffffffffffffffffffff555555555555555555555555555555554000000000000000000000000000000000000000000000000000000000⟩
theorem checked576 : replayPacked (-512) 520 ((ops.drop 544).take 32) output544 = some (output576,854) := by decide
theorem segment576 : silentSegment machine (toConfig (-512) 520 output544) (toConfig (-512) 520 output576) 854 :=
  (replayPacked_sound (-512) 520 ((ops.drop 544).take 32) output544 output576 854 checked576).2
theorem blank_start_576 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output576) 9058 := by
  have h := segAdd machine _ _ _ 8204 854 blank_start_544 segment576
  simpa using h

def output608 : Packed := ⟨2,-141,0xdfffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000000000000000000000000000000000⟩
theorem checked608 : replayPacked (-512) 520 ((ops.drop 576).take 32) output576 = some (output608,893) := by decide
theorem segment608 : silentSegment machine (toConfig (-512) 520 output576) (toConfig (-512) 520 output608) 893 :=
  (replayPacked_sound (-512) 520 ((ops.drop 576).take 32) output576 output608 893 checked608).2
theorem blank_start_608 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output608) 9951 := by
  have h := segAdd machine _ _ _ 9058 893 blank_start_576 segment608
  simpa using h

def output640 : Packed := ⟨0,-315,0xdffffffffffffffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000000000000000000000000000000000000000⟩
theorem checked640 : replayPacked (-512) 520 ((ops.drop 608).take 32) output608 = some (output640,1218) := by decide
theorem segment640 : silentSegment machine (toConfig (-512) 520 output608) (toConfig (-512) 520 output640) 1218 :=
  (replayPacked_sound (-512) 520 ((ops.drop 608).take 32) output608 output640 1218 checked640).2
theorem blank_start_640 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output640) 11169 := by
  have h := segAdd machine _ _ _ 9951 1218 blank_start_608 segment640
  simpa using h

def output672 : Packed := ⟨0,-330,0xdffffffffffffffffffffffffffffffd5555555555555555555555555555555555555555555555555554000000000000000000000000000000000000000000000⟩
theorem checked672 : replayPacked (-512) 520 ((ops.drop 640).take 32) output640 = some (output672,1205) := by decide
theorem segment672 : silentSegment machine (toConfig (-512) 520 output640) (toConfig (-512) 520 output672) 1205 :=
  (replayPacked_sound (-512) 520 ((ops.drop 640).take 32) output640 output672 1205 checked672).2
theorem blank_start_672 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output672) 12374 := by
  have h := segAdd machine _ _ _ 11169 1205 blank_start_640 segment672
  simpa using h

def output704 : Packed := ⟨2,-346,0xdffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaae00000000000000000000000000000000000000000⟩
theorem checked704 : replayPacked (-512) 520 ((ops.drop 672).take 32) output672 = some (output704,1350) := by decide
theorem segment704 : silentSegment machine (toConfig (-512) 520 output672) (toConfig (-512) 520 output704) 1350 :=
  (replayPacked_sound (-512) 520 ((ops.drop 672).take 32) output672 output704 1350 checked704).2
theorem blank_start_704 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output704) 13724 := by
  have h := segAdd machine _ _ _ 12374 1350 blank_start_672 segment704
  simpa using h

def output736 : Packed := ⟨4,-104,0xdffffffffffffffffffffffffff555555555555555555555555555555555555555555555555555555555555555540000000000000000000000000000000000000⟩
theorem checked736 : replayPacked (-512) 520 ((ops.drop 704).take 32) output704 = some (output736,1750) := by decide
theorem segment736 : silentSegment machine (toConfig (-512) 520 output704) (toConfig (-512) 520 output736) 1750 :=
  (replayPacked_sound (-512) 520 ((ops.drop 704).take 32) output704 output736 1750 checked736).2
theorem blank_start_736 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output736) 15474 := by
  have h := segAdd machine _ _ _ 13724 1750 blank_start_704 segment736
  simpa using h

def output768 : Packed := ⟨2,-93,0xdfffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000000000000000000000000000000000⟩
theorem checked768 : replayPacked (-512) 520 ((ops.drop 736).take 32) output736 = some (output768,1661) := by decide
theorem segment768 : silentSegment machine (toConfig (-512) 520 output736) (toConfig (-512) 520 output768) 1661 :=
  (replayPacked_sound (-512) 520 ((ops.drop 736).take 32) output736 output768 1661 checked768).2
theorem blank_start_768 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output768) 17135 := by
  have h := segAdd machine _ _ _ 15474 1661 blank_start_736 segment768
  simpa using h

def output800 : Packed := ⟨0,-395,0xdffffffffffffffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000000000⟩
theorem checked800 : replayPacked (-512) 520 ((ops.drop 768).take 32) output768 = some (output800,2114) := by decide
theorem segment800 : silentSegment machine (toConfig (-512) 520 output768) (toConfig (-512) 520 output800) 2114 :=
  (replayPacked_sound (-512) 520 ((ops.drop 768).take 32) output768 output800 2114 checked800).2
theorem blank_start_800 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output800) 19249 := by
  have h := segAdd machine _ _ _ 17135 2114 blank_start_768 segment800
  simpa using h

def output832 : Packed := ⟨0,-410,0xdffffffffffffffffffd5555555555555555555555555555555555555555555555555555555555555555555555555555555555540000000000000000000000000⟩
theorem checked832 : replayPacked (-512) 520 ((ops.drop 800).take 32) output800 = some (output832,1973) := by decide
theorem segment832 : silentSegment machine (toConfig (-512) 520 output800) (toConfig (-512) 520 output832) 1973 :=
  (replayPacked_sound (-512) 520 ((ops.drop 800).take 32) output800 output832 1973 checked832).2
theorem blank_start_832 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output832) 21222 := by
  have h := segAdd machine _ _ _ 19249 1973 blank_start_800 segment832
  simpa using h

def output864 : Packed := ⟨2,-426,0xdffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaae000000000000000000000⟩
theorem checked864 : replayPacked (-512) 520 ((ops.drop 832).take 32) output832 = some (output864,2118) := by decide
theorem segment864 : silentSegment machine (toConfig (-512) 520 output832) (toConfig (-512) 520 output864) 2118 :=
  (replayPacked_sound (-512) 520 ((ops.drop 832).take 32) output832 output864 2118 checked864).2
theorem blank_start_864 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output864) 23340 := by
  have h := segAdd machine _ _ _ 21222 2118 blank_start_832 segment864
  simpa using h

def output896 : Packed := ⟨4,-56,0xdffffffffffffff555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555400000000000000000⟩
theorem checked896 : replayPacked (-512) 520 ((ops.drop 864).take 32) output864 = some (output896,2646) := by decide
theorem segment896 : silentSegment machine (toConfig (-512) 520 output864) (toConfig (-512) 520 output896) 2646 :=
  (replayPacked_sound (-512) 520 ((ops.drop 864).take 32) output864 output896 2646 checked896).2
theorem blank_start_896 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output896) 25986 := by
  have h := segAdd machine _ _ _ 23340 2646 blank_start_864 segment896
  simpa using h

def output928 : Packed := ⟨2,-45,0xdfffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000⟩
theorem checked928 : replayPacked (-512) 520 ((ops.drop 896).take 32) output896 = some (output928,2429) := by decide
theorem segment928 : silentSegment machine (toConfig (-512) 520 output896) (toConfig (-512) 520 output928) 2429 :=
  (replayPacked_sound (-512) 520 ((ops.drop 896).take 32) output896 output928 2429 checked928).2
theorem blank_start_928 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output928) 28415 := by
  have h := segAdd machine _ _ _ 25986 2429 blank_start_896 segment928
  simpa using h

def output960 : Packed := ⟨0,-475,0xdffffffffeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000000000⟩
theorem checked960 : replayPacked (-512) 520 ((ops.drop 928).take 32) output928 = some (output960,3010) := by decide
theorem segment960 : silentSegment machine (toConfig (-512) 520 output928) (toConfig (-512) 520 output960) 3010 :=
  (replayPacked_sound (-512) 520 ((ops.drop 928).take 32) output928 output960 3010 checked960).2
theorem blank_start_960 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output960) 31425 := by
  have h := segAdd machine _ _ _ 28415 3010 blank_start_928 segment960
  simpa using h

def output992 : Packed := ⟨0,-490,0xdffffffd5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555400000⟩
theorem checked992 : replayPacked (-512) 520 ((ops.drop 960).take 32) output960 = some (output992,2741) := by decide
theorem segment992 : silentSegment machine (toConfig (-512) 520 output960) (toConfig (-512) 520 output992) 2741 :=
  (replayPacked_sound (-512) 520 ((ops.drop 960).take 32) output960 output992 2741 checked992).2
theorem blank_start_992 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output992) 34166 := by
  have h := segAdd machine _ _ _ 31425 2741 blank_start_960 segment992
  simpa using h

def output1024 : Packed := ⟨2,-506,0xdffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaae0⟩
theorem checked1024 : replayPacked (-512) 520 ((ops.drop 992).take 32) output992 = some (output1024,2886) := by decide
theorem segment1024 : silentSegment machine (toConfig (-512) 520 output992) (toConfig (-512) 520 output1024) 2886 :=
  (replayPacked_sound (-512) 520 ((ops.drop 992).take 32) output992 output1024 2886 checked1024).2
theorem blank_start_1024 : silentSegment machine (machine.system.run 0) (toConfig (-512) 520 output1024) 37052 := by
  have h := segAdd machine _ _ _ 34166 2886 blank_start_992 segment1024
  simpa using h
end Shared.Beeping.NPcoNP.Bootstrap284PackedChunks1024

#print axioms Shared.Beeping.NPcoNP.Bootstrap284PackedChunks1024.blank_start_1024
