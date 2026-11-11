import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S047C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100532269 100565037 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 100532269 100565037).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100532269 100565037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100565037 100597805 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 100565037 100597805).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100565037 100597805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100597805 100630573 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 100597805 100630573).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100597805 100630573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100630573 100663341 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 100630573 100663341).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100630573 100663341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 100532269 100597805).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 100532269 ≤ 100565037)
    (by decide : 100565037 ≤ 100597805) block0 block1

theorem join_0_1 : (twinPrimeSegment 100597805 100663341).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 100597805 ≤ 100630573)
    (by decide : 100630573 ≤ 100663341) block2 block3

theorem join_1_0 : (twinPrimeSegment 100532269 100663341).card = 522 := by
  simpa using combineTwinPrimeSegments (by decide : 100532269 ≤ 100597805)
    (by decide : 100597805 ≤ 100663341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 100532269 100663341).card = 522 := join_1_0

end S047C15
end Sude.GeneratedTwinScan
