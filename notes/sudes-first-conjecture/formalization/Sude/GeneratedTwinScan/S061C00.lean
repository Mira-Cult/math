import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127926317 127959085 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 127926317 127959085).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127926317 127959085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127959085 127991853 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 127959085 127991853).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127959085 127991853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127991853 128024621 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 127991853 128024621).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127991853 128024621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128024621 128057389 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 128024621 128057389).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128024621 128057389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 127926317 127991853).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 127926317 ≤ 127959085)
    (by decide : 127959085 ≤ 127991853) block0 block1

theorem join_0_1 : (twinPrimeSegment 127991853 128057389).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 127991853 ≤ 128024621)
    (by decide : 128024621 ≤ 128057389) block2 block3

theorem join_1_0 : (twinPrimeSegment 127926317 128057389).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 127926317 ≤ 127991853)
    (by decide : 127991853 ≤ 128057389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 127926317 128057389).card = 495 := join_1_0

end S061C00
end Sude.GeneratedTwinScan
