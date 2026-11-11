import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133169197 133201965 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 133169197 133201965).card = 105 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133169197 133201965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133201965 133234733 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 133201965 133234733).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133201965 133234733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133234733 133267501 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 133234733 133267501).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133234733 133267501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133267501 133300269 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 133267501 133300269).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133267501 133300269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 133169197 133234733).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 133169197 ≤ 133201965)
    (by decide : 133201965 ≤ 133234733) block0 block1

theorem join_0_1 : (twinPrimeSegment 133234733 133300269).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 133234733 ≤ 133267501)
    (by decide : 133267501 ≤ 133300269) block2 block3

theorem join_1_0 : (twinPrimeSegment 133169197 133300269).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 133169197 ≤ 133234733)
    (by decide : 133234733 ≤ 133300269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 133169197 133300269).card = 476 := join_1_0

end S063C08
end Sude.GeneratedTwinScan
