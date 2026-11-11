import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S038C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81264685 81297453 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 81264685 81297453).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81264685 81297453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81297453 81330221 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 81297453 81330221).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81297453 81330221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81330221 81362989 = 150 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 81330221 81362989).card = 150 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81330221 81362989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81362989 81395757 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 81362989 81395757).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81362989 81395757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 81264685 81330221).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 81264685 ≤ 81297453)
    (by decide : 81297453 ≤ 81330221) block0 block1

theorem join_0_1 : (twinPrimeSegment 81330221 81395757).card = 286 := by
  simpa using combineTwinPrimeSegments (by decide : 81330221 ≤ 81362989)
    (by decide : 81362989 ≤ 81395757) block2 block3

theorem join_1_0 : (twinPrimeSegment 81264685 81395757).card = 509 := by
  simpa using combineTwinPrimeSegments (by decide : 81264685 ≤ 81330221)
    (by decide : 81330221 ≤ 81395757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 81264685 81395757).card = 509 := join_1_0

end S038C12
end Sude.GeneratedTwinScan
