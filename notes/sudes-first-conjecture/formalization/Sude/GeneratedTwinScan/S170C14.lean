import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18931)) 358350893 358383661 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 358350893 358383661).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18931 358350893 358383661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18931)) 358383661 358416429 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 358383661 358416429).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18931 358383661 358416429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18932)) 358416429 358449197 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 358416429 358449197).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18932 358416429 358449197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18933)) 358449197 358481965 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 358449197 358481965).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18933 358449197 358481965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 358350893 358416429).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 358350893 ≤ 358383661)
    (by decide : 358383661 ≤ 358416429) block0 block1

theorem join_0_1 : (twinPrimeSegment 358416429 358481965).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 358416429 ≤ 358449197)
    (by decide : 358449197 ≤ 358481965) block2 block3

theorem join_1_0 : (twinPrimeSegment 358350893 358481965).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 358350893 ≤ 358416429)
    (by decide : 358416429 ≤ 358481965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 358350893 358481965).card = 439 := join_1_0

end S170C14
end Sude.GeneratedTwinScan
