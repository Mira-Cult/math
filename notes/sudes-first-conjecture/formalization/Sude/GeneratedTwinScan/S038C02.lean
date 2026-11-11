import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S038C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79953965 79986733 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 79953965 79986733).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79953965 79986733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79986733 80019501 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 79986733 80019501).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79986733 80019501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80019501 80052269 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 80019501 80052269).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80019501 80052269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80052269 80085037 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 80052269 80085037).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80052269 80085037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 79953965 80019501).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 79953965 ≤ 79986733)
    (by decide : 79986733 ≤ 80019501) block0 block1

theorem join_0_1 : (twinPrimeSegment 80019501 80085037).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 80019501 ≤ 80052269)
    (by decide : 80052269 ≤ 80085037) block2 block3

theorem join_1_0 : (twinPrimeSegment 79953965 80085037).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 79953965 ≤ 80019501)
    (by decide : 80019501 ≤ 80085037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 79953965 80085037).card = 506 := join_1_0

end S038C02
end Sude.GeneratedTwinScan
