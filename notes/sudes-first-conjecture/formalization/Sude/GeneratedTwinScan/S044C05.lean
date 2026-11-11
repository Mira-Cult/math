import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S044C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92930093 92962861 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 92930093 92962861).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92930093 92962861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92962861 92995629 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 92962861 92995629).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92962861 92995629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92995629 93028397 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 92995629 93028397).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92995629 93028397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93028397 93061165 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 93028397 93061165).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93028397 93061165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 92930093 92995629).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 92930093 ≤ 92962861)
    (by decide : 92962861 ≤ 92995629) block0 block1

theorem join_0_1 : (twinPrimeSegment 92995629 93061165).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 92995629 ≤ 93028397)
    (by decide : 93028397 ≤ 93061165) block2 block3

theorem join_1_0 : (twinPrimeSegment 92930093 93061165).card = 514 := by
  simpa using combineTwinPrimeSegments (by decide : 92930093 ≤ 92995629)
    (by decide : 92995629 ≤ 93061165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 92930093 93061165).card = 514 := join_1_0

end S044C05
end Sude.GeneratedTwinScan
