import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S045C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94896173 94928941 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 94896173 94928941).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94896173 94928941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94928941 94961709 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 94928941 94961709).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94928941 94961709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94961709 94994477 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 94961709 94994477).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94961709 94994477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94994477 95027245 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 94994477 95027245).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94994477 95027245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 94896173 94961709).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 94896173 ≤ 94928941)
    (by decide : 94928941 ≤ 94961709) block0 block1

theorem join_0_1 : (twinPrimeSegment 94961709 95027245).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 94961709 ≤ 94994477)
    (by decide : 94994477 ≤ 95027245) block2 block3

theorem join_1_0 : (twinPrimeSegment 94896173 95027245).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 94896173 ≤ 94961709)
    (by decide : 94961709 ≤ 95027245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 94896173 95027245).card = 474 := join_1_0

end S045C04
end Sude.GeneratedTwinScan
