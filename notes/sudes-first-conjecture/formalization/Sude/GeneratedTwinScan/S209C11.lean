import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S209C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20970)) 439746605 439779373 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 439746605 439779373).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20970 439746605 439779373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20971)) 439779373 439812141 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 439779373 439812141).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20971 439779373 439812141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20972)) 439812141 439844909 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 439812141 439844909).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20972 439812141 439844909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20973)) 439844909 439877677 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 439844909 439877677).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20973 439844909 439877677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 439746605 439812141).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 439746605 ≤ 439779373)
    (by decide : 439779373 ≤ 439812141) block0 block1

theorem join_0_1 : (twinPrimeSegment 439812141 439877677).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 439812141 ≤ 439844909)
    (by decide : 439844909 ≤ 439877677) block2 block3

theorem join_1_0 : (twinPrimeSegment 439746605 439877677).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 439746605 ≤ 439812141)
    (by decide : 439812141 ≤ 439877677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 439746605 439877677).card = 438 := join_1_0

end S209C11
end Sude.GeneratedTwinScan
