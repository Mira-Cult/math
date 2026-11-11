import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S200C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20506)) 420479021 420511789 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 420479021 420511789).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20506 420479021 420511789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20507)) 420511789 420544557 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 420511789 420544557).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20507 420511789 420544557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20507)) 420544557 420577325 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 420544557 420577325).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20507 420544557 420577325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20508)) 420577325 420610093 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 420577325 420610093).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20508 420577325 420610093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 420479021 420544557).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 420479021 ≤ 420511789)
    (by decide : 420511789 ≤ 420544557) block0 block1

theorem join_0_1 : (twinPrimeSegment 420544557 420610093).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 420544557 ≤ 420577325)
    (by decide : 420577325 ≤ 420610093) block2 block3

theorem join_1_0 : (twinPrimeSegment 420479021 420610093).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 420479021 ≤ 420544557)
    (by decide : 420544557 ≤ 420610093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 420479021 420610093).card = 478 := join_1_0

end S200C08
end Sude.GeneratedTwinScan
