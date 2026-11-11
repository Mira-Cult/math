import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S066C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139067437 139100205 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 139067437 139100205).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139067437 139100205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139100205 139132973 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 139100205 139132973).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139100205 139132973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139132973 139165741 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 139132973 139165741).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139132973 139165741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139165741 139198509 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 139165741 139198509).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139165741 139198509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 139067437 139132973).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 139067437 ≤ 139100205)
    (by decide : 139100205 ≤ 139132973) block0 block1

theorem join_0_1 : (twinPrimeSegment 139132973 139198509).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 139132973 ≤ 139165741)
    (by decide : 139165741 ≤ 139198509) block2 block3

theorem join_1_0 : (twinPrimeSegment 139067437 139198509).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 139067437 ≤ 139132973)
    (by decide : 139132973 ≤ 139198509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 139067437 139198509).card = 482 := join_1_0

end S066C05
end Sude.GeneratedTwinScan
