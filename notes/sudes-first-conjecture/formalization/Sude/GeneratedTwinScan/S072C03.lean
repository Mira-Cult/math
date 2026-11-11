import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S072C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151388205 151420973 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 151388205 151420973).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151388205 151420973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151420973 151453741 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 151420973 151453741).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151420973 151453741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151453741 151486509 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 151453741 151486509).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151453741 151486509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151486509 151519277 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 151486509 151519277).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151486509 151519277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 151388205 151453741).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 151388205 ≤ 151420973)
    (by decide : 151420973 ≤ 151453741) block0 block1

theorem join_0_1 : (twinPrimeSegment 151453741 151519277).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 151453741 ≤ 151486509)
    (by decide : 151486509 ≤ 151519277) block2 block3

theorem join_1_0 : (twinPrimeSegment 151388205 151519277).card = 508 := by
  simpa using combineTwinPrimeSegments (by decide : 151388205 ≤ 151453741)
    (by decide : 151453741 ≤ 151519277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 151388205 151519277).card = 508 := join_1_0

end S072C03
end Sude.GeneratedTwinScan
