import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97779757 97812525 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 97779757 97812525).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97779757 97812525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97812525 97845293 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 97812525 97845293).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97812525 97845293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97845293 97878061 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 97845293 97878061).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97845293 97878061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97878061 97910829 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 97878061 97910829).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97878061 97910829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 97779757 97845293).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 97779757 ≤ 97812525)
    (by decide : 97812525 ≤ 97845293) block0 block1

theorem join_0_1 : (twinPrimeSegment 97845293 97910829).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 97845293 ≤ 97878061)
    (by decide : 97878061 ≤ 97910829) block2 block3

theorem join_1_0 : (twinPrimeSegment 97779757 97910829).card = 524 := by
  simpa using combineTwinPrimeSegments (by decide : 97779757 ≤ 97845293)
    (by decide : 97845293 ≤ 97910829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 97779757 97910829).card = 524 := join_1_0

end S046C10
end Sude.GeneratedTwinScan
