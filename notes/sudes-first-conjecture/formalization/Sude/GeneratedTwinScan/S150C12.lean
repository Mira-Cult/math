import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S150C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17781)) 316145709 316178477 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 316145709 316178477).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17781 316145709 316178477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17782)) 316178477 316211245 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 316178477 316211245).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17782 316178477 316211245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17783)) 316211245 316244013 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 316211245 316244013).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17783 316211245 316244013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17784)) 316244013 316276781 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 316244013 316276781).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17784 316244013 316276781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 316145709 316211245).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 316145709 ≤ 316178477)
    (by decide : 316178477 ≤ 316211245) block0 block1

theorem join_0_1 : (twinPrimeSegment 316211245 316276781).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 316211245 ≤ 316244013)
    (by decide : 316244013 ≤ 316276781) block2 block3

theorem join_1_0 : (twinPrimeSegment 316145709 316276781).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 316145709 ≤ 316211245)
    (by decide : 316211245 ≤ 316276781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 316145709 316276781).card = 442 := join_1_0

end S150C12
end Sude.GeneratedTwinScan
