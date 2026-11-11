import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S038C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80609325 80642093 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 80609325 80642093).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80609325 80642093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80642093 80674861 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 80642093 80674861).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80642093 80674861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80674861 80707629 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 80674861 80707629).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80674861 80707629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80707629 80740397 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 80707629 80740397).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80707629 80740397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 80609325 80674861).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 80609325 ≤ 80642093)
    (by decide : 80642093 ≤ 80674861) block0 block1

theorem join_0_1 : (twinPrimeSegment 80674861 80740397).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 80674861 ≤ 80707629)
    (by decide : 80707629 ≤ 80740397) block2 block3

theorem join_1_0 : (twinPrimeSegment 80609325 80740397).card = 522 := by
  simpa using combineTwinPrimeSegments (by decide : 80609325 ≤ 80674861)
    (by decide : 80674861 ≤ 80740397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 80609325 80740397).card = 522 := join_1_0

end S038C07
end Sude.GeneratedTwinScan
