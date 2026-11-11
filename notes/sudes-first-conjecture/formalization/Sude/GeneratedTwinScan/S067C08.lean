import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S067C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141557805 141590573 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 141557805 141590573).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141557805 141590573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141590573 141623341 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 141590573 141623341).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141590573 141623341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141623341 141656109 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 141623341 141656109).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141623341 141656109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141656109 141688877 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 141656109 141688877).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141656109 141688877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 141557805 141623341).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 141557805 ≤ 141590573)
    (by decide : 141590573 ≤ 141623341) block0 block1

theorem join_0_1 : (twinPrimeSegment 141623341 141688877).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 141623341 ≤ 141656109)
    (by decide : 141656109 ≤ 141688877) block2 block3

theorem join_1_0 : (twinPrimeSegment 141557805 141688877).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 141557805 ≤ 141623341)
    (by decide : 141623341 ≤ 141688877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 141557805 141688877).card = 482 := join_1_0

end S067C08
end Sude.GeneratedTwinScan
