import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S037C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77856813 77889581 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 77856813 77889581).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77856813 77889581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77889581 77922349 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 77889581 77922349).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77889581 77922349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77922349 77955117 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 77922349 77955117).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77922349 77955117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77955117 77987885 = 144 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 77955117 77987885).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77955117 77987885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 77856813 77922349).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 77856813 ≤ 77889581)
    (by decide : 77889581 ≤ 77922349) block0 block1

theorem join_0_1 : (twinPrimeSegment 77922349 77987885).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 77922349 ≤ 77955117)
    (by decide : 77955117 ≤ 77987885) block2 block3

theorem join_1_0 : (twinPrimeSegment 77856813 77987885).card = 527 := by
  simpa using combineTwinPrimeSegments (by decide : 77856813 ≤ 77922349)
    (by decide : 77922349 ≤ 77987885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 77856813 77987885).card = 527 := join_1_0

end S037C02
end Sude.GeneratedTwinScan
