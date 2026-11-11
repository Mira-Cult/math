import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12918)) 166854701 166887469 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 166854701 166887469).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12918 166854701 166887469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12919)) 166887469 166920237 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 166887469 166920237).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12919 166887469 166920237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12921)) 166920237 166953005 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 166920237 166953005).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12921 166920237 166953005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12922)) 166953005 166985773 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 166953005 166985773).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12922 166953005 166985773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 166854701 166920237).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 166854701 ≤ 166887469)
    (by decide : 166887469 ≤ 166920237) block0 block1

theorem join_0_1 : (twinPrimeSegment 166920237 166985773).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 166920237 ≤ 166953005)
    (by decide : 166953005 ≤ 166985773) block2 block3

theorem join_1_0 : (twinPrimeSegment 166854701 166985773).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 166854701 ≤ 166920237)
    (by decide : 166920237 ≤ 166985773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 166854701 166985773).card = 442 := join_1_0

end S079C09
end Sude.GeneratedTwinScan
