import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133038125 133070893 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 133038125 133070893).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133038125 133070893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133070893 133103661 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 133070893 133103661).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133070893 133103661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133103661 133136429 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 133103661 133136429).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133103661 133136429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133136429 133169197 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 133136429 133169197).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133136429 133169197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 133038125 133103661).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 133038125 ≤ 133070893)
    (by decide : 133070893 ≤ 133103661) block0 block1

theorem join_0_1 : (twinPrimeSegment 133103661 133169197).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 133103661 ≤ 133136429)
    (by decide : 133136429 ≤ 133169197) block2 block3

theorem join_1_0 : (twinPrimeSegment 133038125 133169197).card = 503 := by
  simpa using combineTwinPrimeSegments (by decide : 133038125 ≤ 133103661)
    (by decide : 133103661 ≤ 133169197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 133038125 133169197).card = 503 := join_1_0

end S063C07
end Sude.GeneratedTwinScan
