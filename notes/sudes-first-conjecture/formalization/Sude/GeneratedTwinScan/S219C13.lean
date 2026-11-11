import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S219C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21471)) 460980269 461013037 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 460980269 461013037).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21471 460980269 461013037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21471)) 461013037 461045805 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 461013037 461045805).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21471 461013037 461045805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21472)) 461045805 461078573 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 461045805 461078573).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21472 461045805 461078573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21473)) 461078573 461111341 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 461078573 461111341).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21473 461078573 461111341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 460980269 461045805).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 460980269 ≤ 461013037)
    (by decide : 461013037 ≤ 461045805) block0 block1

theorem join_0_1 : (twinPrimeSegment 461045805 461111341).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 461045805 ≤ 461078573)
    (by decide : 461078573 ≤ 461111341) block2 block3

theorem join_1_0 : (twinPrimeSegment 460980269 461111341).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 460980269 ≤ 461045805)
    (by decide : 461045805 ≤ 461111341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 460980269 461111341).card = 450 := join_1_0

end S219C13
end Sude.GeneratedTwinScan
