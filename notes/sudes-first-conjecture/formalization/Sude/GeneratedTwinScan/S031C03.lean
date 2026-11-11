import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S031C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65404973 65437741 = 152 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 65404973 65437741).card = 152 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65404973 65437741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65437741 65470509 = 145 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 65437741 65470509).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65437741 65470509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65470509 65503277 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 65470509 65503277).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65470509 65503277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65503277 65536045 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 65503277 65536045).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65503277 65536045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 65404973 65470509).card = 297 := by
  simpa using combineTwinPrimeSegments (by decide : 65404973 ≤ 65437741)
    (by decide : 65437741 ≤ 65470509) block0 block1

theorem join_0_1 : (twinPrimeSegment 65470509 65536045).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 65470509 ≤ 65503277)
    (by decide : 65503277 ≤ 65536045) block2 block3

theorem join_1_0 : (twinPrimeSegment 65404973 65536045).card = 568 := by
  simpa using combineTwinPrimeSegments (by decide : 65404973 ≤ 65470509)
    (by decide : 65470509 ≤ 65536045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 65404973 65536045).card = 568 := join_1_0

end S031C03
end Sude.GeneratedTwinScan
