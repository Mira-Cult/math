import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64618541 64651309 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 64618541 64651309).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64618541 64651309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64651309 64684077 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 64651309 64684077).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64651309 64684077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64684077 64716845 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 64684077 64716845).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64684077 64716845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64716845 64749613 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 64716845 64749613).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64716845 64749613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 64618541 64684077).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 64618541 ≤ 64651309)
    (by decide : 64651309 ≤ 64684077) block0 block1

theorem join_0_1 : (twinPrimeSegment 64684077 64749613).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 64684077 ≤ 64716845)
    (by decide : 64716845 ≤ 64749613) block2 block3

theorem join_1_0 : (twinPrimeSegment 64618541 64749613).card = 530 := by
  simpa using combineTwinPrimeSegments (by decide : 64618541 ≤ 64684077)
    (by decide : 64684077 ≤ 64749613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 64618541 64749613).card = 530 := join_1_0

end S030C13
end Sude.GeneratedTwinScan
