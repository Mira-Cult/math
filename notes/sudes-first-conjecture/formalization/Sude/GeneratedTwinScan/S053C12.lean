import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S053C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112721965 112754733 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 112721965 112754733).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112721965 112754733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112754733 112787501 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 112754733 112787501).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112754733 112787501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112787501 112820269 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 112787501 112820269).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112787501 112820269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112820269 112853037 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 112820269 112853037).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112820269 112853037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 112721965 112787501).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 112721965 ≤ 112754733)
    (by decide : 112754733 ≤ 112787501) block0 block1

theorem join_0_1 : (twinPrimeSegment 112787501 112853037).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 112787501 ≤ 112820269)
    (by decide : 112820269 ≤ 112853037) block2 block3

theorem join_1_0 : (twinPrimeSegment 112721965 112853037).card = 521 := by
  simpa using combineTwinPrimeSegments (by decide : 112721965 ≤ 112787501)
    (by decide : 112787501 ≤ 112853037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 112721965 112853037).card = 521 := join_1_0

end S053C12
end Sude.GeneratedTwinScan
