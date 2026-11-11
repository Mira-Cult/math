import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S051C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107216941 107249709 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 107216941 107249709).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107216941 107249709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107249709 107282477 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 107249709 107282477).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107249709 107282477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107282477 107315245 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 107282477 107315245).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107282477 107315245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107315245 107348013 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 107315245 107348013).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107315245 107348013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 107216941 107282477).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 107216941 ≤ 107249709)
    (by decide : 107249709 ≤ 107282477) block0 block1

theorem join_0_1 : (twinPrimeSegment 107282477 107348013).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 107282477 ≤ 107315245)
    (by decide : 107315245 ≤ 107348013) block2 block3

theorem join_1_0 : (twinPrimeSegment 107216941 107348013).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 107216941 ≤ 107282477)
    (by decide : 107282477 ≤ 107348013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 107216941 107348013).card = 511 := join_1_0

end S051C02
end Sude.GeneratedTwinScan
