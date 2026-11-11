import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S221C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21547)) 464257069 464289837 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 464257069 464289837).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21547 464257069 464289837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21548)) 464289837 464322605 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 464289837 464322605).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21548 464289837 464322605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21548)) 464322605 464355373 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 464322605 464355373).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21548 464322605 464355373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21549)) 464355373 464388141 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 464355373 464388141).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21549 464355373 464388141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 464257069 464322605).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 464257069 ≤ 464289837)
    (by decide : 464289837 ≤ 464322605) block0 block1

theorem join_0_1 : (twinPrimeSegment 464322605 464388141).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 464322605 ≤ 464355373)
    (by decide : 464355373 ≤ 464388141) block2 block3

theorem join_1_0 : (twinPrimeSegment 464257069 464388141).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 464257069 ≤ 464322605)
    (by decide : 464322605 ≤ 464388141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 464257069 464388141).card = 434 := join_1_0

end S221C06
end Sude.GeneratedTwinScan
