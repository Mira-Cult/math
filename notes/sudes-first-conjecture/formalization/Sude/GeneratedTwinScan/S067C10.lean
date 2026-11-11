import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S067C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141819949 141852717 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 141819949 141852717).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141819949 141852717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141852717 141885485 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 141852717 141885485).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141852717 141885485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141885485 141918253 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 141885485 141918253).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141885485 141918253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141918253 141951021 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 141918253 141951021).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141918253 141951021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 141819949 141885485).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 141819949 ≤ 141852717)
    (by decide : 141852717 ≤ 141885485) block0 block1

theorem join_0_1 : (twinPrimeSegment 141885485 141951021).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 141885485 ≤ 141918253)
    (by decide : 141918253 ≤ 141951021) block2 block3

theorem join_1_0 : (twinPrimeSegment 141819949 141951021).card = 503 := by
  simpa using combineTwinPrimeSegments (by decide : 141819949 ≤ 141885485)
    (by decide : 141885485 ≤ 141951021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 141819949 141951021).card = 503 := join_1_0

end S067C10
end Sude.GeneratedTwinScan
