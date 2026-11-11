import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S131C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16627)) 276430893 276463661 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 276430893 276463661).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16627 276430893 276463661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16628)) 276463661 276496429 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 276463661 276496429).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16628 276463661 276496429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16629)) 276496429 276529197 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 276496429 276529197).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16629 276496429 276529197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16630)) 276529197 276561965 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 276529197 276561965).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16630 276529197 276561965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 276430893 276496429).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 276430893 ≤ 276463661)
    (by decide : 276463661 ≤ 276496429) block0 block1

theorem join_0_1 : (twinPrimeSegment 276496429 276561965).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 276496429 ≤ 276529197)
    (by decide : 276529197 ≤ 276561965) block2 block3

theorem join_1_0 : (twinPrimeSegment 276430893 276561965).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 276430893 ≤ 276496429)
    (by decide : 276496429 ≤ 276561965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 276430893 276561965).card = 457 := join_1_0

end S131C13
end Sude.GeneratedTwinScan
