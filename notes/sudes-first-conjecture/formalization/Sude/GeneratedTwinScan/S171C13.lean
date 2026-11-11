import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18982)) 360316973 360349741 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 360316973 360349741).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18982 360316973 360349741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18983)) 360349741 360382509 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 360349741 360382509).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18983 360349741 360382509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18984)) 360382509 360415277 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 360382509 360415277).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18984 360382509 360415277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18985)) 360415277 360448045 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 360415277 360448045).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18985 360415277 360448045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 360316973 360382509).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 360316973 ≤ 360349741)
    (by decide : 360349741 ≤ 360382509) block0 block1

theorem join_0_1 : (twinPrimeSegment 360382509 360448045).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 360382509 ≤ 360415277)
    (by decide : 360415277 ≤ 360448045) block2 block3

theorem join_1_0 : (twinPrimeSegment 360316973 360448045).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 360316973 ≤ 360382509)
    (by decide : 360382509 ≤ 360448045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 360316973 360448045).card = 429 := join_1_0

end S171C13
end Sude.GeneratedTwinScan
