import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S249C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22860)) 522584109 522616877 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 522584109 522616877).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22860 522584109 522616877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22861)) 522616877 522649645 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 522616877 522649645).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22861 522616877 522649645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22862)) 522649645 522682413 = 93 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 522649645 522682413).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22862 522649645 522682413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22862)) 522682413 522715181 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 522682413 522715181).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22862 522682413 522715181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 522584109 522649645).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 522584109 ≤ 522616877)
    (by decide : 522616877 ≤ 522649645) block0 block1

theorem join_0_1 : (twinPrimeSegment 522649645 522715181).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 522649645 ≤ 522682413)
    (by decide : 522682413 ≤ 522715181) block2 block3

theorem join_1_0 : (twinPrimeSegment 522584109 522715181).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 522584109 ≤ 522649645)
    (by decide : 522649645 ≤ 522715181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 522584109 522715181).card = 417 := join_1_0

end S249C03
end Sude.GeneratedTwinScan
