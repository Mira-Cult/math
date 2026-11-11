import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S230C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22001)) 484048941 484081709 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 484048941 484081709).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22001 484048941 484081709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22002)) 484081709 484114477 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 484081709 484114477).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22002 484081709 484114477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22003)) 484114477 484147245 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 484114477 484147245).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22003 484114477 484147245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22004)) 484147245 484180013 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 484147245 484180013).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22004 484147245 484180013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 484048941 484114477).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 484048941 ≤ 484081709)
    (by decide : 484081709 ≤ 484114477) block0 block1

theorem join_0_1 : (twinPrimeSegment 484114477 484180013).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 484114477 ≤ 484147245)
    (by decide : 484147245 ≤ 484180013) block2 block3

theorem join_1_0 : (twinPrimeSegment 484048941 484180013).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 484048941 ≤ 484114477)
    (by decide : 484114477 ≤ 484180013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 484048941 484180013).card = 462 := join_1_0

end S230C13
end Sude.GeneratedTwinScan
