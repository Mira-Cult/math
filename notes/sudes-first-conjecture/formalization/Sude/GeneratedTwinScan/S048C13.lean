import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102367277 102400045 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 102367277 102400045).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102367277 102400045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102400045 102432813 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 102400045 102432813).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102400045 102432813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102432813 102465581 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 102432813 102465581).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102432813 102465581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102465581 102498349 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 102465581 102498349).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102465581 102498349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 102367277 102432813).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 102367277 ≤ 102400045)
    (by decide : 102400045 ≤ 102432813) block0 block1

theorem join_0_1 : (twinPrimeSegment 102432813 102498349).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 102432813 ≤ 102465581)
    (by decide : 102465581 ≤ 102498349) block2 block3

theorem join_1_0 : (twinPrimeSegment 102367277 102498349).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 102367277 ≤ 102432813)
    (by decide : 102432813 ≤ 102498349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 102367277 102498349).card = 490 := join_1_0

end S048C13
end Sude.GeneratedTwinScan
