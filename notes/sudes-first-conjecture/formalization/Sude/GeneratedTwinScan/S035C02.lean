import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73662509 73695277 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 73662509 73695277).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73662509 73695277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73695277 73728045 = 152 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 73695277 73728045).card = 152 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73695277 73728045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73728045 73760813 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 73728045 73760813).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73728045 73760813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73760813 73793581 = 146 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 73760813 73793581).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73760813 73793581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 73662509 73728045).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 73662509 ≤ 73695277)
    (by decide : 73695277 ≤ 73728045) block0 block1

theorem join_0_1 : (twinPrimeSegment 73728045 73793581).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 73728045 ≤ 73760813)
    (by decide : 73760813 ≤ 73793581) block2 block3

theorem join_1_0 : (twinPrimeSegment 73662509 73793581).card = 566 := by
  simpa using combineTwinPrimeSegments (by decide : 73662509 ≤ 73728045)
    (by decide : 73728045 ≤ 73793581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 73662509 73793581).card = 566 := join_1_0

end S035C02
end Sude.GeneratedTwinScan
