import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S055C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116785197 116817965 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 116785197 116817965).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116785197 116817965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116817965 116850733 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 116817965 116850733).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116817965 116850733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116850733 116883501 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 116850733 116883501).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116850733 116883501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116883501 116916269 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 116883501 116916269).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116883501 116916269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 116785197 116850733).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 116785197 ≤ 116817965)
    (by decide : 116817965 ≤ 116850733) block0 block1

theorem join_0_1 : (twinPrimeSegment 116850733 116916269).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 116850733 ≤ 116883501)
    (by decide : 116883501 ≤ 116916269) block2 block3

theorem join_1_0 : (twinPrimeSegment 116785197 116916269).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 116785197 ≤ 116850733)
    (by decide : 116850733 ≤ 116916269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 116785197 116916269).card = 499 := join_1_0

end S055C11
end Sude.GeneratedTwinScan
