import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15564)) 242221101 242253869 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 242221101 242253869).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15564 242221101 242253869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15565)) 242253869 242286637 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 242253869 242286637).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15565 242253869 242286637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15566)) 242286637 242319405 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 242286637 242319405).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15566 242286637 242319405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15567)) 242319405 242352173 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 242319405 242352173).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15567 242319405 242352173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 242221101 242286637).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 242221101 ≤ 242253869)
    (by decide : 242253869 ≤ 242286637) block0 block1

theorem join_0_1 : (twinPrimeSegment 242286637 242352173).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 242286637 ≤ 242319405)
    (by decide : 242319405 ≤ 242352173) block2 block3

theorem join_1_0 : (twinPrimeSegment 242221101 242352173).card = 412 := by
  simpa using combineTwinPrimeSegments (by decide : 242221101 ≤ 242286637)
    (by decide : 242286637 ≤ 242352173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 242221101 242352173).card = 412 := join_1_0

end S115C08
end Sude.GeneratedTwinScan
