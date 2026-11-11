import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S233C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22117)) 489160749 489193517 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 489160749 489193517).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22117 489160749 489193517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22118)) 489193517 489226285 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 489193517 489226285).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22118 489193517 489226285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22119)) 489226285 489259053 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 489226285 489259053).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22119 489226285 489259053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22119)) 489259053 489291821 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 489259053 489291821).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22119 489259053 489291821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 489160749 489226285).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 489160749 ≤ 489193517)
    (by decide : 489193517 ≤ 489226285) block0 block1

theorem join_0_1 : (twinPrimeSegment 489226285 489291821).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 489226285 ≤ 489259053)
    (by decide : 489259053 ≤ 489291821) block2 block3

theorem join_1_0 : (twinPrimeSegment 489160749 489291821).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 489160749 ≤ 489226285)
    (by decide : 489226285 ≤ 489291821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 489160749 489291821).card = 415 := join_1_0

end S233C04
end Sude.GeneratedTwinScan
