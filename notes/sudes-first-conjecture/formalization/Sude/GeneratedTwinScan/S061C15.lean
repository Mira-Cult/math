import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129892397 129925165 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 129892397 129925165).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129892397 129925165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129925165 129957933 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 129925165 129957933).card = 102 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129925165 129957933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129957933 129990701 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 129957933 129990701).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129957933 129990701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129990701 130023469 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 129990701 130023469).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129990701 130023469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 129892397 129957933).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 129892397 ≤ 129925165)
    (by decide : 129925165 ≤ 129957933) block0 block1

theorem join_0_1 : (twinPrimeSegment 129957933 130023469).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 129957933 ≤ 129990701)
    (by decide : 129990701 ≤ 130023469) block2 block3

theorem join_1_0 : (twinPrimeSegment 129892397 130023469).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 129892397 ≤ 129957933)
    (by decide : 129957933 ≤ 130023469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 129892397 130023469).card = 480 := join_1_0

end S061C15
end Sude.GeneratedTwinScan
