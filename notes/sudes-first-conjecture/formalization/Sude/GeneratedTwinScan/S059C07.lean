import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124649517 124682285 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 124649517 124682285).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124649517 124682285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124682285 124715053 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 124682285 124715053).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124682285 124715053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124715053 124747821 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 124715053 124747821).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124715053 124747821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124747821 124780589 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 124747821 124780589).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124747821 124780589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 124649517 124715053).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 124649517 ≤ 124682285)
    (by decide : 124682285 ≤ 124715053) block0 block1

theorem join_0_1 : (twinPrimeSegment 124715053 124780589).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 124715053 ≤ 124747821)
    (by decide : 124747821 ≤ 124780589) block2 block3

theorem join_1_0 : (twinPrimeSegment 124649517 124780589).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 124649517 ≤ 124715053)
    (by decide : 124715053 ≤ 124780589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 124649517 124780589).card = 491 := join_1_0

end S059C07
end Sude.GeneratedTwinScan
