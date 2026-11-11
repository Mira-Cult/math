import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S065C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136970285 137003053 = 93 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 136970285 137003053).card = 93 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136970285 137003053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137003053 137035821 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 137003053 137035821).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137003053 137035821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137035821 137068589 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 137035821 137068589).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137035821 137068589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137068589 137101357 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 137068589 137101357).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137068589 137101357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 136970285 137035821).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 136970285 ≤ 137003053)
    (by decide : 137003053 ≤ 137035821) block0 block1

theorem join_0_1 : (twinPrimeSegment 137035821 137101357).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 137035821 ≤ 137068589)
    (by decide : 137068589 ≤ 137101357) block2 block3

theorem join_1_0 : (twinPrimeSegment 136970285 137101357).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 136970285 ≤ 137035821)
    (by decide : 137035821 ≤ 137101357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 136970285 137101357).card = 444 := join_1_0

end S065C05
end Sude.GeneratedTwinScan
