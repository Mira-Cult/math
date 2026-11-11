import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S193C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20142)) 405667885 405700653 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 405667885 405700653).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20142 405667885 405700653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20142)) 405700653 405733421 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 405700653 405733421).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20142 405700653 405733421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20143)) 405733421 405766189 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 405733421 405766189).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20143 405733421 405766189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20144)) 405766189 405798957 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 405766189 405798957).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20144 405766189 405798957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 405667885 405733421).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 405667885 ≤ 405700653)
    (by decide : 405700653 ≤ 405733421) block0 block1

theorem join_0_1 : (twinPrimeSegment 405733421 405798957).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 405733421 ≤ 405766189)
    (by decide : 405766189 ≤ 405798957) block2 block3

theorem join_1_0 : (twinPrimeSegment 405667885 405798957).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 405667885 ≤ 405733421)
    (by decide : 405733421 ≤ 405798957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 405667885 405798957).card = 454 := join_1_0

end S193C07
end Sude.GeneratedTwinScan
