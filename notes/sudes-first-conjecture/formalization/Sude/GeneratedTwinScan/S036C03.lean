import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S036C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75890733 75923501 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 75890733 75923501).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75890733 75923501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75923501 75956269 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 75923501 75956269).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75923501 75956269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75956269 75989037 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 75956269 75989037).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75956269 75989037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75989037 76021805 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 75989037 76021805).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75989037 76021805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 75890733 75956269).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 75890733 ≤ 75923501)
    (by decide : 75923501 ≤ 75956269) block0 block1

theorem join_0_1 : (twinPrimeSegment 75956269 76021805).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 75956269 ≤ 75989037)
    (by decide : 75989037 ≤ 76021805) block2 block3

theorem join_1_0 : (twinPrimeSegment 75890733 76021805).card = 526 := by
  simpa using combineTwinPrimeSegments (by decide : 75890733 ≤ 75956269)
    (by decide : 75956269 ≤ 76021805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 75890733 76021805).card = 526 := join_1_0

end S036C03
end Sude.GeneratedTwinScan
