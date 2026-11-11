import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S066C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138674221 138706989 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 138674221 138706989).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138674221 138706989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138706989 138739757 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 138706989 138739757).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138706989 138739757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138739757 138772525 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 138739757 138772525).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138739757 138772525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138772525 138805293 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 138772525 138805293).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138772525 138805293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 138674221 138739757).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 138674221 ≤ 138706989)
    (by decide : 138706989 ≤ 138739757) block0 block1

theorem join_0_1 : (twinPrimeSegment 138739757 138805293).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 138739757 ≤ 138772525)
    (by decide : 138772525 ≤ 138805293) block2 block3

theorem join_1_0 : (twinPrimeSegment 138674221 138805293).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 138674221 ≤ 138739757)
    (by decide : 138739757 ≤ 138805293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 138674221 138805293).card = 463 := join_1_0

end S066C02
end Sude.GeneratedTwinScan
