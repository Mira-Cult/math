import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147062829 147095597 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 147062829 147095597).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147062829 147095597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147095597 147128365 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 147095597 147128365).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147095597 147128365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147128365 147161133 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 147128365 147161133).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147128365 147161133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147161133 147193901 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 147161133 147193901).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147161133 147193901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 147062829 147128365).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 147062829 ≤ 147095597)
    (by decide : 147095597 ≤ 147128365) block0 block1

theorem join_0_1 : (twinPrimeSegment 147128365 147193901).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 147128365 ≤ 147161133)
    (by decide : 147161133 ≤ 147193901) block2 block3

theorem join_1_0 : (twinPrimeSegment 147062829 147193901).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 147062829 ≤ 147128365)
    (by decide : 147128365 ≤ 147193901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 147062829 147193901).card = 472 := join_1_0

end S070C02
end Sude.GeneratedTwinScan
