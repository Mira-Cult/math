import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S143C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17348)) 300941357 300974125 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 300941357 300974125).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17348 300941357 300974125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17349)) 300974125 301006893 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 300974125 301006893).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17349 300974125 301006893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17350)) 301006893 301039661 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 301006893 301039661).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17350 301006893 301039661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17351)) 301039661 301072429 = 90 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 301039661 301072429).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17351 301039661 301072429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 300941357 301006893).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 300941357 ≤ 300974125)
    (by decide : 300974125 ≤ 301006893) block0 block1

theorem join_0_1 : (twinPrimeSegment 301006893 301072429).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 301006893 ≤ 301039661)
    (by decide : 301039661 ≤ 301072429) block2 block3

theorem join_1_0 : (twinPrimeSegment 300941357 301072429).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 300941357 ≤ 301006893)
    (by decide : 301006893 ≤ 301072429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 300941357 301072429).card = 434 := join_1_0

end S143C08
end Sude.GeneratedTwinScan
