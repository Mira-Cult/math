import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124125229 124157997 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 124125229 124157997).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124125229 124157997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124157997 124190765 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 124157997 124190765).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124157997 124190765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124190765 124223533 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 124190765 124223533).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124190765 124223533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124223533 124256301 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 124223533 124256301).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124223533 124256301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 124125229 124190765).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 124125229 ≤ 124157997)
    (by decide : 124157997 ≤ 124190765) block0 block1

theorem join_0_1 : (twinPrimeSegment 124190765 124256301).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 124190765 ≤ 124223533)
    (by decide : 124223533 ≤ 124256301) block2 block3

theorem join_1_0 : (twinPrimeSegment 124125229 124256301).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 124125229 ≤ 124190765)
    (by decide : 124190765 ≤ 124256301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 124125229 124256301).card = 501 := join_1_0

end S059C03
end Sude.GeneratedTwinScan
