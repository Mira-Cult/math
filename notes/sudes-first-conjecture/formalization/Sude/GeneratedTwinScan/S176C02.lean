import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S176C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19219)) 369360941 369393709 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 369360941 369393709).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19219 369360941 369393709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19220)) 369393709 369426477 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 369393709 369426477).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19220 369393709 369426477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19221)) 369426477 369459245 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 369426477 369459245).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19221 369426477 369459245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19222)) 369459245 369492013 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 369459245 369492013).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19222 369459245 369492013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 369360941 369426477).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 369360941 ≤ 369393709)
    (by decide : 369393709 ≤ 369426477) block0 block1

theorem join_0_1 : (twinPrimeSegment 369426477 369492013).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 369426477 ≤ 369459245)
    (by decide : 369459245 ≤ 369492013) block2 block3

theorem join_1_0 : (twinPrimeSegment 369360941 369492013).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 369360941 ≤ 369426477)
    (by decide : 369426477 ≤ 369492013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 369360941 369492013).card = 442 := join_1_0

end S176C02
end Sude.GeneratedTwinScan
