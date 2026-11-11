import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131334189 131366957 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 131334189 131366957).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131334189 131366957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131366957 131399725 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 131366957 131399725).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131366957 131399725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131399725 131432493 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 131399725 131432493).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131399725 131432493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131432493 131465261 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 131432493 131465261).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131432493 131465261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 131334189 131399725).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 131334189 ≤ 131366957)
    (by decide : 131366957 ≤ 131399725) block0 block1

theorem join_0_1 : (twinPrimeSegment 131399725 131465261).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 131399725 ≤ 131432493)
    (by decide : 131432493 ≤ 131465261) block2 block3

theorem join_1_0 : (twinPrimeSegment 131334189 131465261).card = 526 := by
  simpa using combineTwinPrimeSegments (by decide : 131334189 ≤ 131399725)
    (by decide : 131399725 ≤ 131465261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 131334189 131465261).card = 526 := join_1_0

end S062C10
end Sude.GeneratedTwinScan
