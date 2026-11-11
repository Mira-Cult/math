import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145621037 145653805 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 145621037 145653805).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145621037 145653805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145653805 145686573 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 145653805 145686573).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145653805 145686573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145686573 145719341 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 145686573 145719341).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145686573 145719341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145719341 145752109 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 145719341 145752109).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145719341 145752109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 145621037 145686573).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 145621037 ≤ 145653805)
    (by decide : 145653805 ≤ 145686573) block0 block1

theorem join_0_1 : (twinPrimeSegment 145686573 145752109).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 145686573 ≤ 145719341)
    (by decide : 145719341 ≤ 145752109) block2 block3

theorem join_1_0 : (twinPrimeSegment 145621037 145752109).card = 524 := by
  simpa using combineTwinPrimeSegments (by decide : 145621037 ≤ 145686573)
    (by decide : 145686573 ≤ 145752109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 145621037 145752109).card = 524 := join_1_0

end S069C07
end Sude.GeneratedTwinScan
