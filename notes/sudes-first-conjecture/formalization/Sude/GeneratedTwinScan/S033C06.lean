import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69992493 70025261 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 69992493 70025261).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69992493 70025261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70025261 70058029 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 70025261 70058029).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70025261 70058029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70058029 70090797 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 70058029 70090797).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70058029 70090797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70090797 70123565 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 70090797 70123565).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70090797 70123565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 69992493 70058029).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 69992493 ≤ 70025261)
    (by decide : 70025261 ≤ 70058029) block0 block1

theorem join_0_1 : (twinPrimeSegment 70058029 70123565).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 70058029 ≤ 70090797)
    (by decide : 70090797 ≤ 70123565) block2 block3

theorem join_1_0 : (twinPrimeSegment 69992493 70123565).card = 534 := by
  simpa using combineTwinPrimeSegments (by decide : 69992493 ≤ 70058029)
    (by decide : 70058029 ≤ 70123565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 69992493 70123565).card = 534 := join_1_0

end S033C06
end Sude.GeneratedTwinScan
