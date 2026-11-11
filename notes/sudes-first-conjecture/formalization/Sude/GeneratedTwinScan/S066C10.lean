import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S066C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139722797 139755565 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 139722797 139755565).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139722797 139755565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139755565 139788333 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 139755565 139788333).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139755565 139788333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139788333 139821101 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 139788333 139821101).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139788333 139821101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139821101 139853869 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 139821101 139853869).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139821101 139853869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 139722797 139788333).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 139722797 ≤ 139755565)
    (by decide : 139755565 ≤ 139788333) block0 block1

theorem join_0_1 : (twinPrimeSegment 139788333 139853869).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 139788333 ≤ 139821101)
    (by decide : 139821101 ≤ 139853869) block2 block3

theorem join_1_0 : (twinPrimeSegment 139722797 139853869).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 139722797 ≤ 139788333)
    (by decide : 139788333 ≤ 139853869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 139722797 139853869).card = 494 := join_1_0

end S066C10
end Sude.GeneratedTwinScan
