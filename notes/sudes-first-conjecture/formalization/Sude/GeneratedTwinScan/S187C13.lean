import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S187C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19847)) 393871405 393904173 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 393871405 393904173).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19847 393871405 393904173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19847)) 393904173 393936941 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 393904173 393936941).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19847 393904173 393936941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19848)) 393936941 393969709 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 393936941 393969709).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19848 393936941 393969709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19849)) 393969709 394002477 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 393969709 394002477).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19849 393969709 394002477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 393871405 393936941).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 393871405 ≤ 393904173)
    (by decide : 393904173 ≤ 393936941) block0 block1

theorem join_0_1 : (twinPrimeSegment 393936941 394002477).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 393936941 ≤ 393969709)
    (by decide : 393969709 ≤ 394002477) block2 block3

theorem join_1_0 : (twinPrimeSegment 393871405 394002477).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 393871405 ≤ 393936941)
    (by decide : 393936941 ≤ 394002477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 393871405 394002477).card = 439 := join_1_0

end S187C13
end Sude.GeneratedTwinScan
