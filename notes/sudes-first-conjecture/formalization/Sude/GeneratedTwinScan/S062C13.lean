import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131727405 131760173 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 131727405 131760173).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131727405 131760173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131760173 131792941 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 131760173 131792941).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131760173 131792941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131792941 131825709 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 131792941 131825709).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131792941 131825709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131825709 131858477 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 131825709 131858477).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131825709 131858477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 131727405 131792941).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 131727405 ≤ 131760173)
    (by decide : 131760173 ≤ 131792941) block0 block1

theorem join_0_1 : (twinPrimeSegment 131792941 131858477).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 131792941 ≤ 131825709)
    (by decide : 131825709 ≤ 131858477) block2 block3

theorem join_1_0 : (twinPrimeSegment 131727405 131858477).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 131727405 ≤ 131792941)
    (by decide : 131792941 ≤ 131858477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 131727405 131858477).card = 493 := join_1_0

end S062C13
end Sude.GeneratedTwinScan
