import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91750445 91783213 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 91750445 91783213).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91750445 91783213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91783213 91815981 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 91783213 91815981).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91783213 91815981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91815981 91848749 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 91815981 91848749).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91815981 91848749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91848749 91881517 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 91848749 91881517).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91848749 91881517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 91750445 91815981).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 91750445 ≤ 91783213)
    (by decide : 91783213 ≤ 91815981) block0 block1

theorem join_0_1 : (twinPrimeSegment 91815981 91881517).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 91815981 ≤ 91848749)
    (by decide : 91848749 ≤ 91881517) block2 block3

theorem join_1_0 : (twinPrimeSegment 91750445 91881517).card = 500 := by
  simpa using combineTwinPrimeSegments (by decide : 91750445 ≤ 91815981)
    (by decide : 91815981 ≤ 91881517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 91750445 91881517).card = 500 := join_1_0

end S043C12
end Sude.GeneratedTwinScan
