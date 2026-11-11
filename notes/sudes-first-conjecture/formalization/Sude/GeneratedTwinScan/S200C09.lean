import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S200C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20509)) 420610093 420642861 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 420610093 420642861).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20509 420610093 420642861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20510)) 420642861 420675629 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 420642861 420675629).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20510 420642861 420675629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20511)) 420675629 420708397 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 420675629 420708397).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20511 420675629 420708397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20511)) 420708397 420741165 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 420708397 420741165).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20511 420708397 420741165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 420610093 420675629).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 420610093 ≤ 420642861)
    (by decide : 420642861 ≤ 420675629) block0 block1

theorem join_0_1 : (twinPrimeSegment 420675629 420741165).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 420675629 ≤ 420708397)
    (by decide : 420708397 ≤ 420741165) block2 block3

theorem join_1_0 : (twinPrimeSegment 420610093 420741165).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 420610093 ≤ 420675629)
    (by decide : 420675629 ≤ 420741165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 420610093 420741165).card = 462 := join_1_0

end S200C09
end Sude.GeneratedTwinScan
