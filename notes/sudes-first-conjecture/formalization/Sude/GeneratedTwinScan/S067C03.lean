import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S067C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140902445 140935213 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 140902445 140935213).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140902445 140935213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140935213 140967981 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 140935213 140967981).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140935213 140967981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140967981 141000749 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 140967981 141000749).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140967981 141000749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141000749 141033517 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 141000749 141033517).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141000749 141033517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 140902445 140967981).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 140902445 ≤ 140935213)
    (by decide : 140935213 ≤ 140967981) block0 block1

theorem join_0_1 : (twinPrimeSegment 140967981 141033517).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 140967981 ≤ 141000749)
    (by decide : 141000749 ≤ 141033517) block2 block3

theorem join_1_0 : (twinPrimeSegment 140902445 141033517).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 140902445 ≤ 140967981)
    (by decide : 140967981 ≤ 141033517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 140902445 141033517).card = 512 := join_1_0

end S067C03
end Sude.GeneratedTwinScan
