import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S108C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15068)) 227016749 227049517 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 227016749 227049517).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15068 227016749 227049517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15069)) 227049517 227082285 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 227049517 227082285).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15069 227049517 227082285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15070)) 227082285 227115053 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 227082285 227115053).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15070 227082285 227115053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15071)) 227115053 227147821 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 227115053 227147821).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15071 227115053 227147821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 227016749 227082285).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 227016749 ≤ 227049517)
    (by decide : 227049517 ≤ 227082285) block0 block1

theorem join_0_1 : (twinPrimeSegment 227082285 227147821).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 227082285 ≤ 227115053)
    (by decide : 227115053 ≤ 227147821) block2 block3

theorem join_1_0 : (twinPrimeSegment 227016749 227147821).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 227016749 ≤ 227082285)
    (by decide : 227082285 ≤ 227147821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 227016749 227147821).card = 480 := join_1_0

end S108C04
end Sude.GeneratedTwinScan
