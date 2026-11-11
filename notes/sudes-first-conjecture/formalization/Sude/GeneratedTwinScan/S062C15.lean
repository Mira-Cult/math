import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131989549 132022317 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 131989549 132022317).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131989549 132022317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132022317 132055085 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 132022317 132055085).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132022317 132055085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132055085 132087853 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 132055085 132087853).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132055085 132087853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132087853 132120621 = 145 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 132087853 132120621).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132087853 132120621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 131989549 132055085).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 131989549 ≤ 132022317)
    (by decide : 132022317 ≤ 132055085) block0 block1

theorem join_0_1 : (twinPrimeSegment 132055085 132120621).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 132055085 ≤ 132087853)
    (by decide : 132087853 ≤ 132120621) block2 block3

theorem join_1_0 : (twinPrimeSegment 131989549 132120621).card = 533 := by
  simpa using combineTwinPrimeSegments (by decide : 131989549 ≤ 132055085)
    (by decide : 132055085 ≤ 132120621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 131989549 132120621).card = 533 := join_1_0

end S062C15
end Sude.GeneratedTwinScan
