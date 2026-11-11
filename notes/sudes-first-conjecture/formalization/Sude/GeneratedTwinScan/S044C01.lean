import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S044C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92405805 92438573 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 92405805 92438573).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92405805 92438573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92438573 92471341 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 92438573 92471341).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92438573 92471341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92471341 92504109 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 92471341 92504109).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92471341 92504109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92504109 92536877 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 92504109 92536877).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92504109 92536877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 92405805 92471341).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 92405805 ≤ 92438573)
    (by decide : 92438573 ≤ 92471341) block0 block1

theorem join_0_1 : (twinPrimeSegment 92471341 92536877).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 92471341 ≤ 92504109)
    (by decide : 92504109 ≤ 92536877) block2 block3

theorem join_1_0 : (twinPrimeSegment 92405805 92536877).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 92405805 ≤ 92471341)
    (by decide : 92471341 ≤ 92536877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 92405805 92536877).card = 483 := join_1_0

end S044C01
end Sude.GeneratedTwinScan
