import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125698093 125730861 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 125698093 125730861).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125698093 125730861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125730861 125763629 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 125730861 125763629).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125730861 125763629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125763629 125796397 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 125763629 125796397).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125763629 125796397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125796397 125829165 = 144 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 125796397 125829165).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125796397 125829165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 125698093 125763629).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 125698093 ≤ 125730861)
    (by decide : 125730861 ≤ 125763629) block0 block1

theorem join_0_1 : (twinPrimeSegment 125763629 125829165).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 125763629 ≤ 125796397)
    (by decide : 125796397 ≤ 125829165) block2 block3

theorem join_1_0 : (twinPrimeSegment 125698093 125829165).card = 538 := by
  simpa using combineTwinPrimeSegments (by decide : 125698093 ≤ 125763629)
    (by decide : 125763629 ≤ 125829165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 125698093 125829165).card = 538 := join_1_0

end S059C15
end Sude.GeneratedTwinScan
