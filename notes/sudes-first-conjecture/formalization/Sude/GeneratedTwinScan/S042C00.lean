import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88080429 88113197 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 88080429 88113197).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88080429 88113197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88113197 88145965 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 88113197 88145965).card = 104 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88113197 88145965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88145965 88178733 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 88145965 88178733).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88145965 88178733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88178733 88211501 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 88178733 88211501).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88178733 88211501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 88080429 88145965).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 88080429 ≤ 88113197)
    (by decide : 88113197 ≤ 88145965) block0 block1

theorem join_0_1 : (twinPrimeSegment 88145965 88211501).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 88145965 ≤ 88178733)
    (by decide : 88178733 ≤ 88211501) block2 block3

theorem join_1_0 : (twinPrimeSegment 88080429 88211501).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 88080429 ≤ 88145965)
    (by decide : 88145965 ≤ 88211501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 88080429 88211501).card = 506 := join_1_0

end S042C00
end Sude.GeneratedTwinScan
