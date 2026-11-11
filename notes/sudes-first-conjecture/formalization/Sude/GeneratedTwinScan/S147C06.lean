import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S147C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17581)) 309067821 309100589 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 309067821 309100589).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17581 309067821 309100589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17582)) 309100589 309133357 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 309100589 309133357).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17582 309100589 309133357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17583)) 309133357 309166125 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 309133357 309166125).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17583 309133357 309166125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17584)) 309166125 309198893 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 309166125 309198893).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17584 309166125 309198893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 309067821 309133357).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 309067821 ≤ 309100589)
    (by decide : 309100589 ≤ 309133357) block0 block1

theorem join_0_1 : (twinPrimeSegment 309133357 309198893).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 309133357 ≤ 309166125)
    (by decide : 309166125 ≤ 309198893) block2 block3

theorem join_1_0 : (twinPrimeSegment 309067821 309198893).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 309067821 ≤ 309133357)
    (by decide : 309133357 ≤ 309198893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 309067821 309198893).card = 441 := join_1_0

end S147C06
end Sude.GeneratedTwinScan
