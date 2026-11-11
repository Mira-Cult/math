import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S088C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13648)) 186253357 186286125 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 186253357 186286125).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13648 186253357 186286125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13649)) 186286125 186318893 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 186286125 186318893).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13649 186286125 186318893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13651)) 186318893 186351661 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 186318893 186351661).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13651 186318893 186351661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13652)) 186351661 186384429 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 186351661 186384429).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13652 186351661 186384429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 186253357 186318893).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 186253357 ≤ 186286125)
    (by decide : 186286125 ≤ 186318893) block0 block1

theorem join_0_1 : (twinPrimeSegment 186318893 186384429).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 186318893 ≤ 186351661)
    (by decide : 186351661 ≤ 186384429) block2 block3

theorem join_1_0 : (twinPrimeSegment 186253357 186384429).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 186253357 ≤ 186318893)
    (by decide : 186318893 ≤ 186384429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 186253357 186384429).card = 475 := join_1_0

end S088C13
end Sude.GeneratedTwinScan
