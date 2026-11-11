import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S049C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104202285 104235053 = 141 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 104202285 104235053).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104202285 104235053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104235053 104267821 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 104235053 104267821).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104235053 104267821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104267821 104300589 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 104267821 104300589).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104267821 104300589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104300589 104333357 = 144 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 104300589 104333357).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104300589 104333357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 104202285 104267821).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 104202285 ≤ 104235053)
    (by decide : 104235053 ≤ 104267821) block0 block1

theorem join_0_1 : (twinPrimeSegment 104267821 104333357).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 104267821 ≤ 104300589)
    (by decide : 104300589 ≤ 104333357) block2 block3

theorem join_1_0 : (twinPrimeSegment 104202285 104333357).card = 531 := by
  simpa using combineTwinPrimeSegments (by decide : 104202285 ≤ 104267821)
    (by decide : 104267821 ≤ 104333357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 104202285 104333357).card = 531 := join_1_0

end S049C11
end Sude.GeneratedTwinScan
