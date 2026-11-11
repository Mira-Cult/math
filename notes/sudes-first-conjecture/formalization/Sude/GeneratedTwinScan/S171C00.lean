import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18937)) 358613037 358645805 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 358613037 358645805).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18937 358613037 358645805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18938)) 358645805 358678573 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 358645805 358678573).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18938 358645805 358678573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18939)) 358678573 358711341 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 358678573 358711341).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18939 358678573 358711341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18940)) 358711341 358744109 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 358711341 358744109).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18940 358711341 358744109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 358613037 358678573).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 358613037 ≤ 358645805)
    (by decide : 358645805 ≤ 358678573) block0 block1

theorem join_0_1 : (twinPrimeSegment 358678573 358744109).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 358678573 ≤ 358711341)
    (by decide : 358711341 ≤ 358744109) block2 block3

theorem join_1_0 : (twinPrimeSegment 358613037 358744109).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 358613037 ≤ 358678573)
    (by decide : 358678573 ≤ 358744109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 358613037 358744109).card = 425 := join_1_0

end S171C00
end Sude.GeneratedTwinScan
