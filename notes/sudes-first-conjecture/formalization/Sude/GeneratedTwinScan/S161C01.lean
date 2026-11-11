import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S161C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18379)) 337772589 337805357 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 337772589 337805357).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18379 337772589 337805357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18380)) 337805357 337838125 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 337805357 337838125).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18380 337805357 337838125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18381)) 337838125 337870893 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 337838125 337870893).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18381 337838125 337870893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18382)) 337870893 337903661 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 337870893 337903661).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18382 337870893 337903661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 337772589 337838125).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 337772589 ≤ 337805357)
    (by decide : 337805357 ≤ 337838125) block0 block1

theorem join_0_1 : (twinPrimeSegment 337838125 337903661).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 337838125 ≤ 337870893)
    (by decide : 337870893 ≤ 337903661) block2 block3

theorem join_1_0 : (twinPrimeSegment 337772589 337903661).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 337772589 ≤ 337838125)
    (by decide : 337838125 ≤ 337903661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 337772589 337903661).card = 452 := join_1_0

end S161C01
end Sude.GeneratedTwinScan
