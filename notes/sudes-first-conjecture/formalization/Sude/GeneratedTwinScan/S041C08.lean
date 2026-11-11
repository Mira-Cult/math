import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S041C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87031853 87064621 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 87031853 87064621).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87031853 87064621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87064621 87097389 = 152 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 87064621 87097389).card = 152 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87064621 87097389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87097389 87130157 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 87097389 87130157).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87097389 87130157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87130157 87162925 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 87130157 87162925).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87130157 87162925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 87031853 87097389).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 87031853 ≤ 87064621)
    (by decide : 87064621 ≤ 87097389) block0 block1

theorem join_0_1 : (twinPrimeSegment 87097389 87162925).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 87097389 ≤ 87130157)
    (by decide : 87130157 ≤ 87162925) block2 block3

theorem join_1_0 : (twinPrimeSegment 87031853 87162925).card = 549 := by
  simpa using combineTwinPrimeSegments (by decide : 87031853 ≤ 87097389)
    (by decide : 87097389 ≤ 87162925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 87031853 87162925).card = 549 := join_1_0

end S041C08
end Sude.GeneratedTwinScan
