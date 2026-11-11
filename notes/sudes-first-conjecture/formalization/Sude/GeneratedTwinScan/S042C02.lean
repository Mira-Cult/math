import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88342573 88375341 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 88342573 88375341).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88342573 88375341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88375341 88408109 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 88375341 88408109).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88375341 88408109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88408109 88440877 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 88408109 88440877).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88408109 88440877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88440877 88473645 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 88440877 88473645).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88440877 88473645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 88342573 88408109).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 88342573 ≤ 88375341)
    (by decide : 88375341 ≤ 88408109) block0 block1

theorem join_0_1 : (twinPrimeSegment 88408109 88473645).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 88408109 ≤ 88440877)
    (by decide : 88440877 ≤ 88473645) block2 block3

theorem join_1_0 : (twinPrimeSegment 88342573 88473645).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 88342573 ≤ 88408109)
    (by decide : 88408109 ≤ 88473645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 88342573 88473645).card = 497 := join_1_0

end S042C02
end Sude.GeneratedTwinScan
