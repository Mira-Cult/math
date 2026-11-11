import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91095085 91127853 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 91095085 91127853).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91095085 91127853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91127853 91160621 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 91127853 91160621).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91127853 91160621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91160621 91193389 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 91160621 91193389).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91160621 91193389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91193389 91226157 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 91193389 91226157).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91193389 91226157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 91095085 91160621).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 91095085 ≤ 91127853)
    (by decide : 91127853 ≤ 91160621) block0 block1

theorem join_0_1 : (twinPrimeSegment 91160621 91226157).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 91160621 ≤ 91193389)
    (by decide : 91193389 ≤ 91226157) block2 block3

theorem join_1_0 : (twinPrimeSegment 91095085 91226157).card = 530 := by
  simpa using combineTwinPrimeSegments (by decide : 91095085 ≤ 91160621)
    (by decide : 91160621 ≤ 91226157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 91095085 91226157).card = 530 := join_1_0

end S043C07
end Sude.GeneratedTwinScan
