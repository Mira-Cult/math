import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S053C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112853037 112885805 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 112853037 112885805).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112853037 112885805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112885805 112918573 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 112885805 112918573).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112885805 112918573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112918573 112951341 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 112918573 112951341).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112918573 112951341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112951341 112984109 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 112951341 112984109).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112951341 112984109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 112853037 112918573).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 112853037 ≤ 112885805)
    (by decide : 112885805 ≤ 112918573) block0 block1

theorem join_0_1 : (twinPrimeSegment 112918573 112984109).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 112918573 ≤ 112951341)
    (by decide : 112951341 ≤ 112984109) block2 block3

theorem join_1_0 : (twinPrimeSegment 112853037 112984109).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 112853037 ≤ 112918573)
    (by decide : 112918573 ≤ 112984109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 112853037 112984109).card = 499 := join_1_0

end S053C13
end Sude.GeneratedTwinScan
