import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114032685 114065453 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 114032685 114065453).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114032685 114065453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114065453 114098221 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 114065453 114098221).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114065453 114098221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114098221 114130989 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 114098221 114130989).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114098221 114130989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114130989 114163757 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 114130989 114163757).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114130989 114163757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 114032685 114098221).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 114032685 ≤ 114065453)
    (by decide : 114065453 ≤ 114098221) block0 block1

theorem join_0_1 : (twinPrimeSegment 114098221 114163757).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 114098221 ≤ 114130989)
    (by decide : 114130989 ≤ 114163757) block2 block3

theorem join_1_0 : (twinPrimeSegment 114032685 114163757).card = 538 := by
  simpa using combineTwinPrimeSegments (by decide : 114032685 ≤ 114098221)
    (by decide : 114098221 ≤ 114163757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 114032685 114163757).card = 538 := join_1_0

end S054C06
end Sude.GeneratedTwinScan
