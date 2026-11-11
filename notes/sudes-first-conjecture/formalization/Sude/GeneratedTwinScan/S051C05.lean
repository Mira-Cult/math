import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S051C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107610157 107642925 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 107610157 107642925).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107610157 107642925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107642925 107675693 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 107642925 107675693).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107642925 107675693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107675693 107708461 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 107675693 107708461).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107675693 107708461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107708461 107741229 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 107708461 107741229).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107708461 107741229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 107610157 107675693).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 107610157 ≤ 107642925)
    (by decide : 107642925 ≤ 107675693) block0 block1

theorem join_0_1 : (twinPrimeSegment 107675693 107741229).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 107675693 ≤ 107708461)
    (by decide : 107708461 ≤ 107741229) block2 block3

theorem join_1_0 : (twinPrimeSegment 107610157 107741229).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 107610157 ≤ 107675693)
    (by decide : 107675693 ≤ 107741229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 107610157 107741229).card = 506 := join_1_0

end S051C05
end Sude.GeneratedTwinScan
