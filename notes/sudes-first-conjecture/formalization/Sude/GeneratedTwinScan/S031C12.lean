import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S031C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66584621 66617389 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 66584621 66617389).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66584621 66617389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66617389 66650157 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 66617389 66650157).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66617389 66650157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66650157 66682925 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 66650157 66682925).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66650157 66682925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66682925 66715693 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 66682925 66715693).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66682925 66715693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 66584621 66650157).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 66584621 ≤ 66617389)
    (by decide : 66617389 ≤ 66650157) block0 block1

theorem join_0_1 : (twinPrimeSegment 66650157 66715693).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 66650157 ≤ 66682925)
    (by decide : 66682925 ≤ 66715693) block2 block3

theorem join_1_0 : (twinPrimeSegment 66584621 66715693).card = 524 := by
  simpa using combineTwinPrimeSegments (by decide : 66584621 ≤ 66650157)
    (by decide : 66650157 ≤ 66715693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 66584621 66715693).card = 524 := join_1_0

end S031C12
end Sude.GeneratedTwinScan
