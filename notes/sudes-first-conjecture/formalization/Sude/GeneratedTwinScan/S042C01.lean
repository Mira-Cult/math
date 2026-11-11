import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88211501 88244269 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 88211501 88244269).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88211501 88244269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88244269 88277037 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 88244269 88277037).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88244269 88277037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88277037 88309805 = 145 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 88277037 88309805).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88277037 88309805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88309805 88342573 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 88309805 88342573).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88309805 88342573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 88211501 88277037).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 88211501 ≤ 88244269)
    (by decide : 88244269 ≤ 88277037) block0 block1

theorem join_0_1 : (twinPrimeSegment 88277037 88342573).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 88277037 ≤ 88309805)
    (by decide : 88309805 ≤ 88342573) block2 block3

theorem join_1_0 : (twinPrimeSegment 88211501 88342573).card = 539 := by
  simpa using combineTwinPrimeSegments (by decide : 88211501 ≤ 88277037)
    (by decide : 88277037 ≤ 88342573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 88211501 88342573).card = 539 := join_1_0

end S042C01
end Sude.GeneratedTwinScan
