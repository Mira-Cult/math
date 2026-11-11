import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S187C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19820)) 392822829 392855597 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 392822829 392855597).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19820 392822829 392855597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19821)) 392855597 392888365 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 392855597 392888365).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19821 392855597 392888365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19822)) 392888365 392921133 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 392888365 392921133).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19822 392888365 392921133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19823)) 392921133 392953901 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 392921133 392953901).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19823 392921133 392953901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 392822829 392888365).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 392822829 ≤ 392855597)
    (by decide : 392855597 ≤ 392888365) block0 block1

theorem join_0_1 : (twinPrimeSegment 392888365 392953901).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 392888365 ≤ 392921133)
    (by decide : 392921133 ≤ 392953901) block2 block3

theorem join_1_0 : (twinPrimeSegment 392822829 392953901).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 392822829 ≤ 392888365)
    (by decide : 392888365 ≤ 392953901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 392822829 392953901).card = 434 := join_1_0

end S187C05
end Sude.GeneratedTwinScan
