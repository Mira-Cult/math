import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149684269 149717037 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 149684269 149717037).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149684269 149717037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149717037 149749805 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 149717037 149749805).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149717037 149749805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149749805 149782573 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 149749805 149782573).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149749805 149782573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149782573 149815341 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 149782573 149815341).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149782573 149815341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 149684269 149749805).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 149684269 ≤ 149717037)
    (by decide : 149717037 ≤ 149749805) block0 block1

theorem join_0_1 : (twinPrimeSegment 149749805 149815341).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 149749805 ≤ 149782573)
    (by decide : 149782573 ≤ 149815341) block2 block3

theorem join_1_0 : (twinPrimeSegment 149684269 149815341).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 149684269 ≤ 149749805)
    (by decide : 149749805 ≤ 149815341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 149684269 149815341).card = 498 := join_1_0

end S071C06
end Sude.GeneratedTwinScan
