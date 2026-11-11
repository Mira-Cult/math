import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S064C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135004205 135036973 = 149 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 135004205 135036973).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135004205 135036973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135036973 135069741 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 135036973 135069741).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135036973 135069741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135069741 135102509 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 135069741 135102509).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135069741 135102509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135102509 135135277 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 135102509 135135277).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135102509 135135277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 135004205 135069741).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 135004205 ≤ 135036973)
    (by decide : 135036973 ≤ 135069741) block0 block1

theorem join_0_1 : (twinPrimeSegment 135069741 135135277).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 135069741 ≤ 135102509)
    (by decide : 135102509 ≤ 135135277) block2 block3

theorem join_1_0 : (twinPrimeSegment 135004205 135135277).card = 517 := by
  simpa using combineTwinPrimeSegments (by decide : 135004205 ≤ 135069741)
    (by decide : 135069741 ≤ 135135277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 135004205 135135277).card = 517 := join_1_0

end S064C06
end Sude.GeneratedTwinScan
