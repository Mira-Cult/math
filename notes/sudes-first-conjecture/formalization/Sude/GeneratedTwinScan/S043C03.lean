import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90570797 90603565 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 90570797 90603565).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90570797 90603565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90603565 90636333 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 90603565 90636333).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90603565 90636333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90636333 90669101 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 90636333 90669101).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90636333 90669101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90669101 90701869 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 90669101 90701869).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90669101 90701869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 90570797 90636333).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 90570797 ≤ 90603565)
    (by decide : 90603565 ≤ 90636333) block0 block1

theorem join_0_1 : (twinPrimeSegment 90636333 90701869).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 90636333 ≤ 90669101)
    (by decide : 90669101 ≤ 90701869) block2 block3

theorem join_1_0 : (twinPrimeSegment 90570797 90701869).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 90570797 ≤ 90636333)
    (by decide : 90636333 ≤ 90701869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 90570797 90701869).card = 506 := join_1_0

end S043C03
end Sude.GeneratedTwinScan
