import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S053C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112590893 112623661 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 112590893 112623661).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112590893 112623661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112623661 112656429 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 112623661 112656429).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112623661 112656429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112656429 112689197 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 112656429 112689197).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112656429 112689197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112689197 112721965 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 112689197 112721965).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112689197 112721965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 112590893 112656429).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 112590893 ≤ 112623661)
    (by decide : 112623661 ≤ 112656429) block0 block1

theorem join_0_1 : (twinPrimeSegment 112656429 112721965).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 112656429 ≤ 112689197)
    (by decide : 112689197 ≤ 112721965) block2 block3

theorem join_1_0 : (twinPrimeSegment 112590893 112721965).card = 525 := by
  simpa using combineTwinPrimeSegments (by decide : 112590893 ≤ 112656429)
    (by decide : 112656429 ≤ 112721965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 112590893 112721965).card = 525 := join_1_0

end S053C11
end Sude.GeneratedTwinScan
