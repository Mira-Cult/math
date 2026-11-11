import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69599277 69632045 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 69599277 69632045).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69599277 69632045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69632045 69664813 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 69632045 69664813).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69632045 69664813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69664813 69697581 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 69664813 69697581).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69664813 69697581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69697581 69730349 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 69697581 69730349).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69697581 69730349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 69599277 69664813).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 69599277 ≤ 69632045)
    (by decide : 69632045 ≤ 69664813) block0 block1

theorem join_0_1 : (twinPrimeSegment 69664813 69730349).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 69664813 ≤ 69697581)
    (by decide : 69697581 ≤ 69730349) block2 block3

theorem join_1_0 : (twinPrimeSegment 69599277 69730349).card = 537 := by
  simpa using combineTwinPrimeSegments (by decide : 69599277 ≤ 69664813)
    (by decide : 69664813 ≤ 69730349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 69599277 69730349).card = 537 := join_1_0

end S033C03
end Sude.GeneratedTwinScan
