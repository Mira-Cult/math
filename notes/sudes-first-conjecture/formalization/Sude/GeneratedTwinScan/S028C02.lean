import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S028C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 58982445 59015213 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 58982445 59015213).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 58982445 59015213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59015213 59047981 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 59015213 59047981).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59015213 59047981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59047981 59080749 = 143 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 59047981 59080749).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59047981 59080749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59080749 59113517 = 153 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 59080749 59113517).card = 153 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59080749 59113517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 58982445 59047981).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 58982445 ≤ 59015213)
    (by decide : 59015213 ≤ 59047981) block0 block1

theorem join_0_1 : (twinPrimeSegment 59047981 59113517).card = 296 := by
  simpa using combineTwinPrimeSegments (by decide : 59047981 ≤ 59080749)
    (by decide : 59080749 ≤ 59113517) block2 block3

theorem join_1_0 : (twinPrimeSegment 58982445 59113517).card = 545 := by
  simpa using combineTwinPrimeSegments (by decide : 58982445 ≤ 59047981)
    (by decide : 59047981 ≤ 59113517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 58982445 59113517).card = 545 := join_1_0

end S028C02
end Sude.GeneratedTwinScan
