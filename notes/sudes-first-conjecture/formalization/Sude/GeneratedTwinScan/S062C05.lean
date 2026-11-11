import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130678829 130711597 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 130678829 130711597).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130678829 130711597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130711597 130744365 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 130711597 130744365).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130711597 130744365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130744365 130777133 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 130744365 130777133).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130744365 130777133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130777133 130809901 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 130777133 130809901).card = 104 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130777133 130809901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 130678829 130744365).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 130678829 ≤ 130711597)
    (by decide : 130711597 ≤ 130744365) block0 block1

theorem join_0_1 : (twinPrimeSegment 130744365 130809901).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 130744365 ≤ 130777133)
    (by decide : 130777133 ≤ 130809901) block2 block3

theorem join_1_0 : (twinPrimeSegment 130678829 130809901).card = 509 := by
  simpa using combineTwinPrimeSegments (by decide : 130678829 ≤ 130744365)
    (by decide : 130744365 ≤ 130809901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 130678829 130809901).card = 509 := join_1_0

end S062C05
end Sude.GeneratedTwinScan
