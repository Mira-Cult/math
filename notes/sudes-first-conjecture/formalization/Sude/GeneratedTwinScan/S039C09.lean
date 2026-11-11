import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S039C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82968621 83001389 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 82968621 83001389).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82968621 83001389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83001389 83034157 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 83001389 83034157).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83001389 83034157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83034157 83066925 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 83034157 83066925).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83034157 83066925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83066925 83099693 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 83066925 83099693).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83066925 83099693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 82968621 83034157).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 82968621 ≤ 83001389)
    (by decide : 83001389 ≤ 83034157) block0 block1

theorem join_0_1 : (twinPrimeSegment 83034157 83099693).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 83034157 ≤ 83066925)
    (by decide : 83066925 ≤ 83099693) block2 block3

theorem join_1_0 : (twinPrimeSegment 82968621 83099693).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 82968621 ≤ 83034157)
    (by decide : 83034157 ≤ 83099693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 82968621 83099693).card = 520 := join_1_0

end S039C09
end Sude.GeneratedTwinScan
