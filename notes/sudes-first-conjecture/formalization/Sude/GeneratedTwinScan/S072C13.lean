import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S072C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152698925 152731693 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 152698925 152731693).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152698925 152731693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152731693 152764461 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 152731693 152764461).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152731693 152764461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152764461 152797229 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 152764461 152797229).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152764461 152797229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152797229 152829997 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 152797229 152829997).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152797229 152829997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 152698925 152764461).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 152698925 ≤ 152731693)
    (by decide : 152731693 ≤ 152764461) block0 block1

theorem join_0_1 : (twinPrimeSegment 152764461 152829997).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 152764461 ≤ 152797229)
    (by decide : 152797229 ≤ 152829997) block2 block3

theorem join_1_0 : (twinPrimeSegment 152698925 152829997).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 152698925 ≤ 152764461)
    (by decide : 152764461 ≤ 152829997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 152698925 152829997).card = 501 := join_1_0

end S072C13
end Sude.GeneratedTwinScan
