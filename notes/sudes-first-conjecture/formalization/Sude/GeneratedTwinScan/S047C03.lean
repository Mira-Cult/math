import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S047C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98959405 98992173 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 98959405 98992173).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98959405 98992173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98992173 99024941 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 98992173 99024941).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98992173 99024941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99024941 99057709 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 99024941 99057709).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99024941 99057709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99057709 99090477 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 99057709 99090477).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99057709 99090477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 98959405 99024941).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 98959405 ≤ 98992173)
    (by decide : 98992173 ≤ 99024941) block0 block1

theorem join_0_1 : (twinPrimeSegment 99024941 99090477).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 99024941 ≤ 99057709)
    (by decide : 99057709 ≤ 99090477) block2 block3

theorem join_1_0 : (twinPrimeSegment 98959405 99090477).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 98959405 ≤ 99024941)
    (by decide : 99024941 ≤ 99090477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 98959405 99090477).card = 501 := join_1_0

end S047C03
end Sude.GeneratedTwinScan
