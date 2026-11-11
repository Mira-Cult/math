import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124387373 124420141 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 124387373 124420141).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124387373 124420141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124420141 124452909 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 124420141 124452909).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124420141 124452909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124452909 124485677 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 124452909 124485677).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124452909 124485677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124485677 124518445 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 124485677 124518445).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124485677 124518445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 124387373 124452909).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 124387373 ≤ 124420141)
    (by decide : 124420141 ≤ 124452909) block0 block1

theorem join_0_1 : (twinPrimeSegment 124452909 124518445).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 124452909 ≤ 124485677)
    (by decide : 124485677 ≤ 124518445) block2 block3

theorem join_1_0 : (twinPrimeSegment 124387373 124518445).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 124387373 ≤ 124452909)
    (by decide : 124452909 ≤ 124518445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 124387373 124518445).card = 469 := join_1_0

end S059C05
end Sude.GeneratedTwinScan
