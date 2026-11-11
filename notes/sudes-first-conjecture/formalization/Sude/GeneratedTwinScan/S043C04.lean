import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90701869 90734637 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 90701869 90734637).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90701869 90734637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90734637 90767405 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 90734637 90767405).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90734637 90767405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90767405 90800173 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 90767405 90800173).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90767405 90800173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90800173 90832941 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 90800173 90832941).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90800173 90832941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 90701869 90767405).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 90701869 ≤ 90734637)
    (by decide : 90734637 ≤ 90767405) block0 block1

theorem join_0_1 : (twinPrimeSegment 90767405 90832941).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 90767405 ≤ 90800173)
    (by decide : 90800173 ≤ 90832941) block2 block3

theorem join_1_0 : (twinPrimeSegment 90701869 90832941).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 90701869 ≤ 90767405)
    (by decide : 90767405 ≤ 90832941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 90701869 90832941).card = 506 := join_1_0

end S043C04
end Sude.GeneratedTwinScan
