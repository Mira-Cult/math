import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S028C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59637805 59670573 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 59637805 59670573).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59637805 59670573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59670573 59703341 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 59670573 59703341).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59670573 59703341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59703341 59736109 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 59703341 59736109).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59703341 59736109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59736109 59768877 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 59736109 59768877).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59736109 59768877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 59637805 59703341).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 59637805 ≤ 59670573)
    (by decide : 59670573 ≤ 59703341) block0 block1

theorem join_0_1 : (twinPrimeSegment 59703341 59768877).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 59703341 ≤ 59736109)
    (by decide : 59736109 ≤ 59768877) block2 block3

theorem join_1_0 : (twinPrimeSegment 59637805 59768877).card = 537 := by
  simpa using combineTwinPrimeSegments (by decide : 59637805 ≤ 59703341)
    (by decide : 59703341 ≤ 59768877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 59637805 59768877).card = 537 := join_1_0

end S028C07
end Sude.GeneratedTwinScan
