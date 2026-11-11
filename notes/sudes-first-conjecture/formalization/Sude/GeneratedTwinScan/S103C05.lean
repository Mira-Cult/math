import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S103C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14720)) 216662061 216694829 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 216662061 216694829).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14720 216662061 216694829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14721)) 216694829 216727597 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 216694829 216727597).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14721 216694829 216727597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14722)) 216727597 216760365 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 216727597 216760365).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14722 216727597 216760365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14723)) 216760365 216793133 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 216760365 216793133).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14723 216760365 216793133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 216662061 216727597).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 216662061 ≤ 216694829)
    (by decide : 216694829 ≤ 216727597) block0 block1

theorem join_0_1 : (twinPrimeSegment 216727597 216793133).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 216727597 ≤ 216760365)
    (by decide : 216760365 ≤ 216793133) block2 block3

theorem join_1_0 : (twinPrimeSegment 216662061 216793133).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 216662061 ≤ 216727597)
    (by decide : 216727597 ≤ 216793133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 216662061 216793133).card = 431 := join_1_0

end S103C05
end Sude.GeneratedTwinScan
