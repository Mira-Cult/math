import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S101C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14581)) 212598829 212631597 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 212598829 212631597).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14581 212598829 212631597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14583)) 212631597 212664365 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 212631597 212664365).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14583 212631597 212664365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14584)) 212664365 212697133 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 212664365 212697133).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14584 212664365 212697133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14585)) 212697133 212729901 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 212697133 212729901).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14585 212697133 212729901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 212598829 212664365).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 212598829 ≤ 212631597)
    (by decide : 212631597 ≤ 212664365) block0 block1

theorem join_0_1 : (twinPrimeSegment 212664365 212729901).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 212664365 ≤ 212697133)
    (by decide : 212697133 ≤ 212729901) block2 block3

theorem join_1_0 : (twinPrimeSegment 212598829 212729901).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 212598829 ≤ 212664365)
    (by decide : 212664365 ≤ 212729901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 212598829 212729901).card = 480 := join_1_0

end S101C06
end Sude.GeneratedTwinScan
